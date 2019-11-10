if [ ! -d "$HOME/.elan/toolchains/" ]; then
  curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none -y
   echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile
   source $HOME/.profile
fi
source ~/.elan/env
elan toolchain install leanprover-community/lean:nightly-2019-11-06
elan toolchain install 3.4.2
elan default leanprover-community/lean:nightly # 3.4.2
lean -v
leanpkg build
