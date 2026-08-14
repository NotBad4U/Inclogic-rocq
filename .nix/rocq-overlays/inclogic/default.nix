## Local package definition for this development.
## It is not (yet) in nixpkgs, so we describe it here; the coq-nix-toolbox
## overrides `version` with the local sources when building the main job.
## Doc: https://nixos.org/manual/nixpkgs/stable/#sec-language-coq

{
  lib,
  mkRocqDerivation,
  stdlib,
  mathcomp-boot,
  mathcomp-finmap,
  relation-algebra,
  rocq-elpi,
  version ? null,
}:

mkRocqDerivation {
  pname = "inclogic";
  owner = "NotBad4U";
  repo = "Inclogic-rocq";

  inherit version;
  ## No release yet: the version is always given explicitly
  ## (a path, a branch or a PR) by `.nix/config.nix` or the command line.
  defaultVersion = null;

  propagatedBuildInputs = [
    stdlib
    mathcomp-boot
    mathcomp-finmap
    relation-algebra
    rocq-elpi
  ];

  ## `Makefile.conf` and `.Makefile.d` are not in the repository: the
  ## `Makefile.conf: _CoqProject` rule of the `Makefile` regenerates them with
  ## `rocq makefile`, against the Rocq of this build.

  meta = {
    description = "Mechanized Incorrectness Logic in Rocq";
    ## The repository carries no LICENSE file yet; add one here when it does.
    # license = lib.licenses.mit;
  };
}
