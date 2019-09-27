
import system.io

open io io.proc io.fs

def git_clone (repo : string) : io unit :=
io.cmd { cmd := "git", args := ["checkout",repo] } >>= put_str_ln

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

def main : io unit :=
    do put_str_ln "hello world",
       xs <- read_lines "pkgs/list",
       print xs,
       mkdir "build",
       env.set_cwd "build",
       xs.mmap' git_clone
