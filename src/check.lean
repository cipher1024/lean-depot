
import system.io leanpkg.git leanpkg.main

def io.cmd' (args : io.process.spawn_args) : io unit :=
leanpkg.exec_cmd args
-- do child ← io.proc.spawn args,
--   exitv ← io.proc.wait child,
--   when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
--   return ()

open io io.proc io.fs

def git_checkout_hash (hash : string) : io unit :=
io.cmd' {cmd := "git", args := ["checkout","-f","--detach",hash]}

def git_pull_master : io unit :=
io.cmd' {cmd := "git", args := ["checkout","pull","-f","origin","master"]}

def git_checkout_tag (tag : string) : io unit :=
io.cmd' {cmd := "git", args := ["checkout",sformat!"tags/{tag}","-f","--detach"]}

def git_fetch : io unit :=
io.cmd' { cmd := "git", args := ["fetch","--all"] }

def string.is_prefix_of_aux : string.iterator → string.iterator → ℕ → bool
| i j 0 := tt
| i j (nat.succ n) :=
  i.curr = j.curr ∧ string.is_prefix_of_aux i.next j.next n

def string.is_prefix_of (x y : string) : bool :=
x.length ≤ y.length ∧ string.is_prefix_of_aux x.mk_iterator y.mk_iterator x.length

def string.drop (x : string) (n : ℕ) : string :=
(x.mk_iterator.nextn n).next_to_string

def string.replace_prefix (x y z : string) : string :=
if y.is_prefix_of x
  then z ++ x.drop y.length
  else x

def add_token (repo : string) : io string :=
do some s ← io.env.get "GITHUB_TOKEN" | pure repo,
   return $ (repo.replace_prefix "https://github.com" (sformat!"https://{s}@github.com"))
                 .replace_prefix "https://www.github.com" (sformat!"https://{s}@www.github.com")

def git_clone (repo : string) : option string → io unit
| none :=
do put_str_ln sformat!"clone {repo}",
   io.cmd' { cmd := "git", args := ["clone",repo] }
| (some dir) :=
do put_str_ln sformat!"clone {repo}",
   io.cmd' { cmd := "git", args := ["clone",repo,dir] }

def list_dir (dir : string) : io (list string) :=
do ls ← (list.filter (≠ "") ∘ string.split (= '\n')) <$> io.cmd { cmd := "ls", args := [dir] },
   return $ ls.map $ λ fn, sformat!"{dir}/{fn}"

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
(config_file dir : string)
(url : list string)
(commit : option string)
(update : bool)
(description : string)
(author : option string )
(left_over     : list (string × toml.value))
-- (pkg_left_over : list (string × toml.value))

instance : has_to_string package :=
{ to_string := λ p,
  sformat!"{{ config_file := {repr p.config_file},
  url := {repr p.url},
  dir := {repr p.dir},
  commit := {repr p.commit},
  update := {p.update},
  description := {p.description},
  author := {p.author} }" }

structure app_args :=
(tag : string)
(lean_version : string)
-- (mathlib : bool)

def usage {α} : io α :=
io.fail "usage: check (--makefile LEAN_VERSION TAG | --update)"

-- def snapshots' (args : app_args) (ps : list package) (ms : list leanpkg.manifest) :
--   (string × list (string × string × leanpkg.manifest)) :=
-- (args.tag, ps.zip_with (λ p m, (p.url, p.dir, m)) ms)


-- list.map (prod.map id prod.fst) <$> (m.to_list.mmap $ λ ⟨p,v⟩, (prod.mk p ∘ prod.fst) <$> v.to_list)

-- def snapshots (m : vmap) : list (ℕ × list (string × string)) :=
-- list.enum $
-- list.map (prod.map id prod.fst) <$> (m.to_list.mmap $ λ ⟨p,v⟩, (prod.mk p ∘ prod.fst) <$> v.to_list)

def dir_part : list string → string
| [] := ""
| [x] := x
| [x,y] := sformat!"{x}/{y}"
| (x :: xs) := dir_part xs

-- def list_packages : io (list package) :=
-- do xs <- read_lines "pkgs/list",
--    let xs := ((xs.filter (≠ "")).map trim).filter (λ s, ¬ string.is_prefix_of "--" s),
--    return $ xs.map $ λ d, ⟨d,dir_part (split_path d),none⟩

def split_ext : string → list string := string.split (= '.')

def package.name (p : package) : string :=
".".intercalate (split_ext (split_path p.config_file).ilast).init

def parse_file (fn : string) : io toml.value :=
do cnts ← io.fs.read_file fn,
   match parser.run toml.File cnts with
  | sum.inl err :=
    io.fail $ "toml parse error in " ++ fn ++ "\n\n" ++ err
  | sum.inr res := return res
   end

def split_off : toml.value → string → option (toml.value × list (string × toml.value))
| (toml.value.table cs) k :=
  match cs.partition (λ c : string × toml.value, c.fst = k) with
  | ([],_) := none
  | ((k,v) ::_, xs) := some (v,xs)
  end
| _ _ := none

class is_toml_value (α : Type*) :=
(read_toml : toml.value → option α)

export is_toml_value (read_toml)

instance : is_toml_value string :=
{ read_toml := λ v, match v with
                    | (toml.value.str s) := some s
                    | _ := none
                    end }

instance : is_toml_value bool :=
{ read_toml := λ v, match v with
                    | (toml.value.bool s) := some s
                    | _ := none
                    end }

instance {α} [is_toml_value α] : is_toml_value (list α) :=
{ read_toml := λ v, match v with
                    | (toml.value.array s) := s.mmap (read_toml _)
                    | _ := none
                    end }

def lookup_toml (α) [is_toml_value α] (v : toml.value) (key : string) : option α :=
v.lookup key >>= read_toml _

def lookup_optional_toml (α) [is_toml_value α] (v : toml.value) (key : string) : option (option α) :=
match v.lookup key with
| (some v) := some <$> read_toml _ v
| none := some none
end

def split_off' (α) [is_toml_value α] (v : toml.value) (key : string) : option (α × toml.value) :=
split_off v key >>= λ ⟨v,xs⟩,
prod.mk <$> read_toml _ v <*> pure (toml.value.table xs)

def split_off_optional (α) [is_toml_value α] (v : toml.value) (key : string) : option (option α × toml.value) :=
match split_off v key with
| (some (v,xs)) := prod.mk <$> (some <$> read_toml _ v) <*> pure (toml.value.table xs)
| none := some (none,v)
end

-- #exit
def package.to_toml (p : package) : toml.value :=
toml.value.table $
let sha := match p.commit with
           | some sha := [("commit",toml.value.str sha)]
           | none := []
           end,
    author := match p.author with
           | some sha := [("author",toml.value.str sha)]
           | none := []
           end in
("package", toml.value.table $
  [ ("url", toml.value.array $ toml.value.str <$> p.url),
    ("description", toml.value.str p.description),
    ("auto_update", toml.value.bool p.update) ]
  ++ sha ++ author ) :: p.left_over

def package.from_toml (fn : string) (t : toml.value) : option package :=
do (pkg,xs) ← split_off t "package",
   url    ← list.ret <$> lookup_toml string pkg "url" <|>
            lookup_toml (list string) pkg "url" ,
   desc   ← lookup_toml string pkg "description",
   update ← lookup_toml bool   pkg "auto_update",
   commit ← lookup_optional_toml string pkg "commit",
   author ← lookup_optional_toml string pkg "author",
   pure { config_file := fn, url := url,
          update := update,
          commit := commit, left_over := xs,
          author := author,
          description := desc,
          dir := dir_part (split_path url.ilast) }

def parse_package_file (fn : string) : io package :=
do val ← parse_file fn,
   some pkg ← pure $ package.from_toml fn val | io.fail sformat!"invalid file format for {fn}",
   pure pkg

def rewrite_package_file (fn : package) : io unit :=
leanpkg.write_file fn.config_file (repr fn.to_toml)

-- #eval parse_package_file "pkgs/mathlib.toml" >>= print

def list_packages' : io (list package) :=
do xs <- list_dir "pkgs",
   let xs := xs.filter $ λ fn, (split_ext fn).ilast = "toml",
   xs.mmap parse_package_file

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
-- def checkout_snapshot :
--   string × list (string × string × leanpkg.manifest) →
--   io (string × list string)
-- | (tag,m) :=
--    do { let sd := sformat!"build/{tag}",
--         mkdir sd tt,
--         put_str_ln sd,
--         -- let m := rbmap.from_list m,
--         xs ← m.mmap $ λ ⟨url,dir,(m : leanpkg.manifest)⟩,
--           with_cwd sd $
--           do { ex ← dir_exists dir,
--                put_str_ln dir,
--                when (¬ ex) $ git_clone url dir,
--                git_fetch,
--                env.set_cwd dir,
--                catch (git_checkout_tag tag) (λ _ : io.error, (return () : io unit)),
--                -- put_str_ln r.url,
--                -- env.get_cwd >>= put_str_ln,
--                leanpkg.write_manifest
--                  { dependencies := m.dependencies.map mk_local,
--                    lean_version := "3.4.2", .. m },
--                return sformat!"{sd}/{dir}"},
--         return (sd, xs) }
-- #exit
def update_package_desc :
  list (package × leanpkg.manifest) → io unit | ps :=
ps.mmap' $ λ p, rewrite_package_file p.1

def checkout_snapshot' (args : app_args) :
  list (package × leanpkg.manifest) →
  io (string)
| ps :=
   do { let sd := sformat!"build/{args.tag}",
        mkdir sd tt,
        put_str_ln sd,
        -- let m := rbmap.from_list m,
        ps.mmap' $ λ ⟨p,(m : leanpkg.manifest)⟩,
          with_cwd sd $
          do { let dir := p.dir,
               ex ← dir_exists dir,
               put_str_ln dir,
               when (¬ ex) $ git_clone p.url.head dir,
               git_fetch,
               env.set_cwd dir,
               match p.commit with
               | some sha := git_checkout_hash sha
               | none     := catch (git_checkout_tag args.tag) (λ _ : io.error, (return () : io unit))
               end,
               -- put_str_ln r.url,
               -- env.get_cwd >>= put_str_ln,
               leanpkg.write_manifest
                 { dependencies := m.dependencies.map mk_local,
                   lean_version := args.lean_version, .. m },
               return sformat!"{sd}/{dir}"},
        return (sd) }

def dep_to_target_name (m : rbmap string (package × leanpkg.manifest)) : leanpkg.dependency → option string
| { src := (leanpkg.source.git url _ _), .. } := m.find (canonicalize_url url) >>= λ ⟨p,_⟩, some sformat!"{p.dir}.pkg"
| { src := (leanpkg.source.path _), .. } := none

-- #exit
def write_Makefile (dir : string) (ps : list $ package × leanpkg.manifest) : io unit :=
with_cwd dir $
do let m : rbmap string (package × leanpkg.manifest) :=
           rbmap.from_list (ps.map $ λ ⟨p,q⟩, (p.url.head, p, q)) ,
   h ← mk_file_handle "Makefile" mode.write,
   let deps := ps.map $ λ p, sformat!"{p.1.dir}.pkg",

   let all_tgt := sformat!"all: {\" \".intercalate deps}\n\n",
   let init_tgt := sformat!"init:
\techo [failure] > failure.toml
\techo \"\" > snapshot.toml
\n",
   write h (all_tgt ++ init_tgt).to_char_buffer,
   ps.mmap' $ λ p : package × _,
     do { some sha ← pure p.1.commit | pure (),
          let deps := p.2.dependencies.filter_map $ dep_to_target_name m,
          let header := sformat!"{p.1.dir}.pkg: init {\" \".intercalate deps}\n",
          let echo := sformat!"echo \"{p.1.name} = {{ git = \\\"{p.1.url}\\\", rev = \\\"{sha}\\\" } \"",
          let cmds   := sformat!"\t@cd {p.1.dir} && leanpkg test || ({echo} >> ../../failure.toml && false)",
          let echo   := sformat!"
\t@echo \"[snapshot.{p.1.name}]\" >> snapshot.toml
\t@echo \"git = {p.1.url.map repr}\" >> snapshot.toml
\t@echo \"rev = \\\"{sha}\\\"\" >> snapshot.toml
\t@echo \"desc = \\\"{p.1.description}\\\"\" >> snapshot.toml
\t@echo \"\" >> snapshot.toml\n\n",
          write h (header ++ cmds ++ echo).to_char_buffer },
   close h

def setup_snapshots (n : app_args) : io unit :=
do xs ← list_packages',
   -- print xs,
   mkdir "build/root" tt,
   ys ← with_cwd "build/root" $
   do { xs.mmap $ λ r, do {
          let dir := r.dir,
          ex ← dir_exists dir,
          when (¬ ex) $ git_clone r.url.head r.dir,
          r ← if r.update ∧ r.commit.is_none
            then do c ← leanpkg.git_head_revision r.dir,
                    pure { commit := c, .. r }
            else pure r,
          prod.mk r <$> leanpkg.manifest.from_file (dir ++ "/" ++ leanpkg.leanpkg_toml_fn) } },
   -- let zs := (ys.bind leanpkg.manifest.dependencies).foldl (flip dep_versions) (mk_rbmap _ _),
   -- let s := snapshots' n xs ys,
   -- let s : list (ℕ × list (string × string)) := snapshots zs,
   -- xs.mmap' $ io.put_str_ln ∘ to_string,
   update_package_desc ys,
   dir ← checkout_snapshot' n ys,
   write_Makefile dir ys,
   pure ()
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

def parse_args : io (option app_args) :=
do xs ← cmdline_args | usage,
   match xs with
       | ["--makefile",vers,tag] := pure (some { tag := tag, lean_version := vers })
       | ["--update"] := pure none
       | _ := usage
       end

def update_pkgs : io unit :=
do xs ← list_packages',
   -- print xs,
   mkdir "build/root" tt,
   let xs := xs.filter $ λ p, p.update,
   ys ← with_cwd "build/root" $
   do { xs.mmap $ λ r, do {
        let dir := r.dir,
        ex ← dir_exists dir,
        if ¬ ex
          then git_clone r.url.head r.dir
          else git_pull_master,
        c ← leanpkg.git_head_revision r.dir,
        let r := { commit := c, .. r },
        prod.mk r <$> leanpkg.manifest.from_file (dir ++ "/" ++ leanpkg.leanpkg_toml_fn) } },
   update_package_desc ys,
   return ()

def main : io unit :=
do some opt ← parse_args | update_pkgs,
   setup_snapshots opt,
   -- mkdir "snapshot" tt,
   -- let snap_name := "snapshot-lean-3.4.2--2019-10",
   -- io.cmd { cmd := "git",args := ["clone", "--single-branch", "--branch", "snapshot", "http://gitlab.com/simon.hudon/lean-depot", "snapshot"] },
   -- io.cmd { cmd := "cp", args := [sformat!"build/{snap_name}/snapshot.toml",
   --                                sformat!"snapshot/{snap_name}.toml"] },
   -- io.cmd { cmd := "cp", args := [sformat!"build/{snap_name}/failure.toml",
   --                                sformat!"snapshot/{snap_name}-failure.toml"] },
   -- io.cmd { cmd := "git",
   --          args := ["add",sformat!"snapshot/{snap_name}-failure.toml",
   --                   sformat!"snapshot/{snap_name}.toml"],
   --          cwd := "snapshot" },
   -- print s,
   pure ()
-- list_dir "pkgs" >>= print

-- def main' : io unit :=
-- do -- cmd' { cmd := "elan", args := ["default","3.4.2"] },
--    args ← parse_args,
--    (s,xs) ← setup_snapshots args,
--    -- env.set_cwd "/Users/simon/lean/lean-depot",
--    -- _,
--    s ← prod.mk s <$> xs.mmap (λ y, prod.mk y <$> make y),
--    leanpkg.write_file "results.toml" (repr $ build_result_file [s]),
--    cmd' { cmd := "cat", args := ["results.toml"] },
--    pure ()

-- #eval main


-- #eval env.set_cwd "/Users/simon/lean/lean-depot"
-- #eval do
--   env.set_cwd "/Users/simon/lean/lean-depot",
--   main

-- #eval do
--   env.set_cwd "/Users/simon/lean/lean-depot",
--   send_mail "simon.hudon@gmail.com" "mail sent from Lean" "leanpkg.toml"
