#! /bin/sh

# Create folder with leanpkg.toml with two dependencies.
mkdir -p combined_lib
cp leanpkg.toml combined_lib/
cd combined_lib/
sed -i 's/name.*/name = "combined_lib"/g' leanpkg.toml
sed -i '/path/d' leanpkg.toml

# Get last revision of topologygame:
LAST_COMMIT=$(git ls-remote https://github.com/mmasdeu/topologygame.git HEAD | cut -f1)
echo "topologygame = {git = \"https://github.com/mmasdeu/topologygame\", rev = \"$LAST_COMMIT\"}" >> leanpkg.toml

# Generate a zip in dist/library.zip

git init
LATEST_BROWSER_LEAN=$(curl -s -N https://raw.githubusercontent.com/leanprover-community/mathlib/master/leanpkg.toml | grep -m1 lean_version | cut -d'"' -f2 | cut -d':' -f2)
elan override set leanprover-community/lean:$LATEST_BROWSER_LEAN
leanproject --no-lean-upgrade up
rm -rf _target/deps/mathlib/test
rm -rf _target/deps/mathlib/scripts
rm -rf _target/deps/mathlib/roadmap          
cd ..
./lean-web-editor/mk_library.py -i combined_lib | python ./lean-web-editor/detect_errors.py