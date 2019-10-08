
import system.io leanpkg.git leanpkg.main

def io.cmd' (args : io.process.spawn_args) : io unit :=
do child ← io.proc.spawn args,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return ()

open io io.proc io.fs

def git_checkout_hash (hash : string) : io unit :=
io.cmd' {cmd := "git", args := ["checkout","-f","--detach",hash]}

def git_checkout_tag (tag : string) : io unit :=
io.cmd' {cmd := "git", args := ["checkout",sformat!"tags/{tag}","-f","--detach"]}

def git_fetch : io unit :=
io.cmd' { cmd := "git", args := ["fetch"] }

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
(p.split (= '/')).filter (λ s, ¬ s.is_empty)

-- #eval -- split_path "a/b"

-- do xs <- read_lines "pkgs/list",
--    let xs := (xs.filter (≠ "")).map trim,
--    print $ xs.map $ list.ilast ∘ split_path

-- open native

-- def dep_versions' (l : leanpkg.source) (m : rbmap string (list string)) : rbmap string (list string) :=
open leanpkg.source

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

def mathlib_sha := ("https://github.com/leanprover-community/mathlib",
                   ["019b2364cadb1dd8b30c9f13c602d61c19d3b6ea",
                    "14e10bbda42f928bdc6f9664e8d9826e598a68fe",
                    "257fd84fe98927ff4a5ffe044f68c4e9d235cc75",
                    "2c84af163dbc83c6eb6a94a03d5c25f25b6b8623",
                    "410ae5d9ec48843f0c2bf6787faafaa83c766623",
                    "5329bf3af9ecea916d32362dc28fd391075a63a1",
                    "58909bd424209739a2214961eefaa012fb8a18d2",
                    "9b0fd36245ae958aeda9e10d79650801f63cd3ae",
                    "b1920f599efe036cefbd02916aba9f687793c8c8",
                    "d60d1616958787ccb9842dc943534f90ea0bab64"])

-- #eval mathlib_sha.2.length

structure package :=
(url dir : string)

structure app_args :=
(tag : string)
(mathlib : bool)

def usage {α} : io α :=
io.fail "usage: check TAG [--mathlib]"

def snapshots' (args : app_args) (ps : list package) (ms : list leanpkg.manifest) :
  (string × list (string × string × leanpkg.manifest)) :=
(args.tag, ps.zip_with (λ p m, (p.url, p.dir, m)) ms)


-- list.map (prod.map id prod.fst) <$> (m.to_list.mmap $ λ ⟨p,v⟩, (prod.mk p ∘ prod.fst) <$> v.to_list)

-- def snapshots (m : vmap) : list (ℕ × list (string × string)) :=
-- list.enum $
-- list.map (prod.map id prod.fst) <$> (m.to_list.mmap $ λ ⟨p,v⟩, (prod.mk p ∘ prod.fst) <$> v.to_list)

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
   finally (env.set_cwd d *> m) (env.set_cwd d')

def mk_local (d : leanpkg.dependency) : leanpkg.dependency :=
{ src := match d.src with
         | (path p) := path p
         | (git u c b) := path $ "../../" ++ dir_part (split_path $ canonicalize_url u)
         end
  .. d }

-- #exit
-- (xs : list package) (ys : list leanpkg.manifest) :
def checkout_snapshot :
  string × list (string × string × leanpkg.manifest) →
  io (string × list string)
| (tag,m) :=
   do { let sd := sformat!"build/{tag}",
        mkdir sd tt,
        put_str_ln sd,
        -- let m := rbmap.from_list m,
        xs ← m.mmap $ λ ⟨url,dir,(m : leanpkg.manifest)⟩,
          with_cwd sd $
          do { ex ← dir_exists dir,
               put_str_ln dir,
               when (¬ ex) $ git_clone url dir,
               git_fetch,
               env.set_cwd dir,
               catch (git_checkout_tag tag) (λ _ : io.error, (return () : io unit)),
               -- put_str_ln r.url,
               -- env.get_cwd >>= put_str_ln,
               leanpkg.write_manifest
                 { dependencies := m.dependencies.map mk_local,
                   lean_version := "3.4.2", .. m },
               return sformat!"{sd}/{dir}"},
        return (sd, xs) }

def setup_snapshots (n : app_args) : io (string × list string) :=
do xs ← list_packages,
   -- print xs,
   mkdir "build/root" tt,
   ys ← with_cwd "build/root" $
   do { let xs := if n.mathlib
                     then xs.filter $ λ p, p.dir = "leanprover-community/mathlib"
                     else xs,
        xs.mmap $ λ r, do {
          let dir := r.dir,
          ex ← dir_exists dir,
          when (¬ ex) $ git_clone r.url r.dir,
          leanpkg.manifest.from_file $ dir ++ "/" ++ leanpkg.leanpkg_toml_fn } },
   -- let zs := (ys.bind leanpkg.manifest.dependencies).foldl (flip dep_versions) (mk_rbmap _ _),
   let s := snapshots' n xs ys,
   -- let s : list (ℕ × list (string × string)) := snapshots zs,
   -- print xs,
   checkout_snapshot s
   -- return ds.join,

def try (cmd : io unit) : io bool :=
io.catch (tt <$ cmd) (λ _, pure ff)

def make (s : string) : io bool :=
do put_str_ln sformat!">> build: {s}",
   env.get_cwd >>= put_str_ln,
   m ← leanpkg.manifest.from_file sformat!"{s}/{leanpkg.leanpkg_toml_fn}",
   try $ with_cwd s $ do
     leanpkg.configure >> leanpkg.make []

def build_result_file (xs : list (string × list (string × bool))) : toml.value :=
toml.value.table $ xs.map $ prod.map id $ toml.value.table ∘ list.map (prod.map id toml.value.bool)

def spawn_piped (p1 p2 : process.spawn_args) : io unit :=
do h1 ← proc.spawn { stdout := process.stdio.piped .. p1 },
   h2 ← proc.spawn { stdin  := process.stdio.piped .. p2 },
   io.iterate () (λ x : unit,
       do done ← is_eof h1.stdout,
          if done
            then close h2.stdin >> return none
            else do
              c ← read h1.stdout 1024,
              write h2.stdin c,
              return $ some ()),
   wait h1, wait h2,
   return ()

def send_mail (addr subject : string) (attachment : string) : io unit :=
do -- spawn_piped { cmd := "uuencode", args := [attachment,(split_path attachment).ilast] }
   --             { cmd := "mail", args := ["-s",subject,addr] }
   cmd' { cmd := "sh", args := ["send_mail.sh",attachment,(split_path attachment).ilast,subject,addr] }



-- uuencode /usr/bin/xxx.c MyFile.c | mail -s "mailing my c file" youremail@yourdomain.com

def list.head' {α} : list α → option α
| [] := none
| (x :: xs) := x

def select_snapshot : io (option string) :=
list.head' <$> cmdline_args

def parse_args : io app_args :=
do n :: xs ← cmdline_args | usage,
   b ← match xs with
       | ["--mathlib"] := pure tt
       | [] := pure ff
       | _ := usage
       end,
   pure { tag := n, mathlib := b }

def main : io unit :=
do -- cmd' { cmd := "elan", args := ["default","3.4.2"] },
   args ← parse_args,
   (s,xs) ← setup_snapshots args,
   -- env.set_cwd "/Users/simon/lean/lean-depot",
   -- _,
   s ← prod.mk s <$> xs.mmap (λ y, prod.mk y <$> make y),
   leanpkg.write_file "results.toml" (repr $ build_result_file [s]),
   cmd' { cmd := "cat", args := ["results.toml"] },
   pure ()

-- #eval env.set_cwd "/Users/simon/lean/lean-depot"
-- #eval do
--   env.set_cwd "/Users/simon/lean/lean-depot",
--   main

-- #eval do
--   env.set_cwd "/Users/simon/lean/lean-depot",
--   send_mail "simon.hudon@gmail.com" "mail sent from Lean" "leanpkg.toml"
