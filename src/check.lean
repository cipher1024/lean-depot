
import system.io leanpkg.git leanpkg.main

def io.cmd' (args : io.process.spawn_args) : io unit :=
do child ← io.proc.spawn args,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return ()

open io io.proc io.fs

def git_checkout_hash (hash : string) : io unit :=
io.cmd' {cmd := "git", args := ["checkout", "--detach", hash]}

def git_clone (repo : string) : option string → io unit
| none :=
do put_str_ln sformat!"clone {repo}",
   io.cmd' { cmd := "git", args := ["clone",repo] }
| (some dir) :=
do put_str_ln sformat!"clone {repo}",
   io.cmd' { cmd := "git", args := ["clone",repo,dir] }

def read_lines (fn : string) : io (list string) :=
do h ← mk_file_handle fn io.mode.read ff,
   r ← iterate [] $ λ r,
      do { done ← is_eof h,
           if done
              then return none
              else do
                c ← get_line h,
                return $ some (c.to_string :: r) },
   return r.reverse

def list.take_while {α} (p : α → Prop) [decidable_pred p] : list α → list α
| [] := []
| (x :: xs) :=
  if p x then x :: list.take_while xs
         else []

def trim : string → string :=
list.as_string ∘ list.take_while (not ∘ char.is_whitespace) ∘ list.drop_while char.is_whitespace ∘ string.to_list

def split_path (p : string) : list string :=
p.split (= '/')

-- #eval -- split_path "a/b"

-- do xs <- read_lines "pkgs/list",
--    let xs := (xs.filter (≠ "")).map trim,
--    print $ xs.map $ list.ilast ∘ split_path

-- open native

-- def dep_versions' (l : leanpkg.source) (m : rbmap string (list string)) : rbmap string (list string) :=
open leanpkg.source
#check leanpkg.source

@[reducible]
def vmap := rbmap string $ rbmap (string × string) unit

-- #exit

def conv_url : rbmap string string :=
rbmap.from_list
[ ("https://github.com/leanprover/mathlib", "https://github.com/leanprover-community/mathlib") ]

def canonicalize_url (s : string) : string :=
let xs := list.reverse (s.to_list.reverse.drop_while (= '/')),
    ys := if ".git".to_list.is_suffix_of xs
             then list.as_string $ xs.take (xs.length - 4)
             else list.as_string xs in
(conv_url.find ys).get_or_else ys

def dep_versions (l : leanpkg.dependency) (m : vmap) : vmap :=
match l.src with
| (path p) := m
| (git url sha br) :=
  let url := canonicalize_url url,
      xs := (m.find url).get_or_else (mk_rbmap _ _) in
  m.insert url (xs.insert (sha, br.get_or_else "") ())
end

instance {α β} [has_lt α] [has_to_string α] [has_to_string β] : has_to_string (rbmap α β) :=
⟨ to_string ∘ rbtree.to_list ⟩

def snapshots (m : vmap) : list (ℕ × list (string × string)) :=
list.enum $
list.map (prod.map id prod.fst) <$> (m.to_list.mmap $ λ ⟨p,v⟩, (prod.mk p ∘ prod.fst) <$> v.to_list)

structure package :=
(url dir : string)

def dir_part : list string → string
| [] := ""
| [x] := x
| [x,y] := sformat!"{x}/{y}"
| (x :: xs) := dir_part xs

def string.is_prefix_of_aux : string.iterator → string.iterator → ℕ → bool
| i j 0 := tt
| i j (nat.succ n) :=
  i.curr = j.curr ∧ string.is_prefix_of_aux i.next j.next n

def string.is_prefix_of (x y : string) : bool :=
x.length ≤ y.length ∧ string.is_prefix_of_aux x.mk_iterator y.mk_iterator x.length

def list_packages : io (list package) :=
do xs <- read_lines "pkgs/list",
   let xs := ((xs.filter (≠ "")).map trim).filter (λ s, ¬ string.is_prefix_of "--" s),
   return $ xs.map $ λ d, ⟨d,dir_part (split_path d)⟩

def with_cwd {α} (d : string) (m : io α) : io α :=
do d' ← env.get_cwd,
   env.set_cwd d *> m <* env.set_cwd d'

def mk_local (d : leanpkg.dependency) : leanpkg.dependency :=
{ src := match d.src with
         | (path p) := path p
         | (git u c b) := path $ "../../" ++ dir_part (split_path u)
         end
  .. d }

def setup_snapshots : io (list string) :=
do xs ← list_packages,
   -- print xs,
   mkdir "build/root" tt,
   ys ← with_cwd "build/root" $
      xs.mmap $ λ r, do {
        let dir := r.dir,
        ex ← dir_exists dir,
        when (¬ ex) $ git_clone r.url r.dir,
        leanpkg.manifest.from_file $ dir ++ "/" ++ leanpkg.leanpkg_toml_fn },
   let zs := (ys.bind leanpkg.manifest.dependencies).foldl (flip dep_versions) (mk_rbmap _ _),
   let s := snapshots zs,
   ds ← s.mmap $ λ ⟨n,m⟩,
   do { let sd := sformat!"build/snapshot_{n}",
        mkdir sd tt,
        do { let m := rbmap.from_list m,
             (xs.zip ys).mmap $ λ ⟨r,y⟩,
               with_cwd sd $
               do ex ← dir_exists r.dir,
                  when (¬ ex) $ git_clone r.url r.dir,
                  env.set_cwd r.dir,
                  match m.find r.url with
                  | some h := git_checkout_hash h
                  | none   := return ()
                  end,
                  -- put_str_ln r.url,
                  -- env.get_cwd >>= put_str_ln,
                  leanpkg.write_manifest { dependencies := y.dependencies.map mk_local .. y },
                  return sformat!"{sd}/{r.dir}" } },
   -- zs.to_list.mmap' (λ l, print l >> io.put_str_ln "\n"),
   return ds.join

def make (s : string) : io unit :=
do m ← leanpkg.manifest.from_file sformat!"{s}/{leanpkg.leanpkg_toml_fn}",
   put_str_ln s,
   with_cwd s $ leanpkg.configure >> leanpkg.make []
   -- cmd' { cmd := "lean", args := ["--make"] ++ m.effective_path },
   -- cmd' { cmd := "lean", args := ["--make"] ++ m.effective_path }

def main : io unit :=
do -- env.set_cwd "/Users/simon/lean/lean-depot",
   sd ← setup_snapshots,
   -- env.set_cwd "/Users/simon/lean/lean-depot",
   sd.mmap' make

-- #eval env.set_cwd "/Users/simon/lean/lean-depot"
-- #eval main
