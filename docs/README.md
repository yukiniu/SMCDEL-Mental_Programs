# Documentation Tooling for SMCDEL

This folder will contain `.svg` files that are used in the documentation.
They are not tracked by git as they are auto-generated: the `preHaddock`
defined in `../Setup.hs` will run `make -B` in this folder here.

Then `collector.sh` will create the file `generator.hs` which will then
actually create all the `.svg` files. Note that `generator.hs` uses the
command `stack runghc` and assumes that the whole library has already
been built. Hence, to generate the haddocks, run this:

```
stack build
stack haddock
```
