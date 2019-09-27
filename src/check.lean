
import system.io

def io.cmd' (args : io.process.spawn_args) : io unit :=
do child ← io.proc.spawn args,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return ()

open io io.proc io.fs

def git_clone (repo : string) : io unit :=
do put_str_ln sformat!"clone {repo}",
   io.cmd' { cmd := "git", args := ["clone",repo] }

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

def main : io unit :=
    do put_str_ln "hello world",
       xs <- read_lines "pkgs/list",
       print xs,
       mkdir "build",
       env.set_cwd "build",
       xs.mmap' $ git_clone ∘ trim
