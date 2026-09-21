## Local package definition for CompCert.
##
## CompCert is a `coqPackages` package (it is driven by its own `./configure`,
## not by `rocq makefile`), hence `.nix/coq-overlays` rather than
## `.nix/rocq-overlays`.  The `coq` it is built against is the compatibility
## layer that `.nix/config.nix` keeps in step with `rocq-core`, so the `.vo`
## files land in the same `lib/coq/<version>/user-contrib` that `rocq` scans.
##
## Amended copy of the nixpkgs derivation: as of this writing nixpkgs only
## knows up to 3.17, whose `./configure` stops at Rocq 9.1, so the package is
## filtered out of the 9.2 set entirely.  (nixpkgs' `defaultVersion` switch
## reads `(case (range "8.15" "9.1") "3.17")`, which yields `null` — i.e. no
## package at all — for Rocq 9.2.)
##
## BEWARE: CompCert 3.18 ships a stale `VERSION` file that still reads
## `version=3.17`, and `ccomp`/`clightgen` print it verbatim, as does the
## `Info.version` block of generated Clight.  So the toolchain reports 3.17
## even though this really is 3.18 — check `Changelog.md`, whose top entry is
## `# Release 3.18`, or note that `lib/Iteration.v` declares no axioms and
## that `./configure` probes `rocq --print-version`, both 3.18 changes.  The
## hash below is 3.18's and differs from nixpkgs' 3.17 hash
## (`sha256-RRc39FUe2sHQdO/ybwA3B7o31qfxcUkgah6I20i0ElE=`).  3.18 is the first release that
## accepts Rocq 9.0 to 9.2, i.e. exactly the range the bundles cover.  Drop
## this overlay once nixpkgs ships 3.18.
##
## Two deliberate differences from nixpkgs, both because only Rocq 9.x matters
## here:
##  * none of the Coq 8.x compatibility patches, which 3.18 does not need;
##  * no split `lib` output.  The Rocq development is installed into
##    `$out/lib/coq/<version>/user-contrib/compcert`, so that listing plain
##    `compcert` in `.nix/config.nix` is enough for `rocq` to resolve
##    `From compcert Require Import ...` through ROCQPATH.  nixpkgs splits it
##    off for the sake of VST, which has to point at the directory explicitly.

{
  lib,
  mkCoqDerivation,
  coq,
  flocq,
  MenhirLib,
  makeWrapper,
  stdenv,
  tools ? stdenv.cc,
  version ? null,
}:

let
  ## https://compcert.org/man/manual002.html
  targets = {
    x86_64-linux = "x86_64-linux";
    aarch64-linux = "aarch64-linux";
    aarch64-darwin = "aarch64-macos";
    riscv32-linux = "rv32-linux";
    riscv64-linux = "rv64-linux";
  };

  target =
    targets.${stdenv.hostPlatform.system}
      or (throw "Unsupported system: ${stdenv.hostPlatform.system}");
in

mkCoqDerivation {
  pname = "compcert";
  owner = "AbsInt";

  inherit version;
  releaseRev = v: "v${v}";

  defaultVersion =
    lib.switch [ coq.coq-version ]
      [
        {
          cases = [ (lib.versions.range "9.0" "9.2") ];
          out = "3.18";
        }
      ]
      null;

  release."3.18".hash = "sha256-WadkhdtAgh+Tz8RxHT7NEV8RMeBBXxzJ1pLQPs94vfo=";

  strictDeps = true;

  nativeBuildInputs = with coq.ocamlPackages; [
    makeWrapper
    ocaml
    findlib
    menhir
    coq
  ];
  buildInputs = with coq.ocamlPackages; [ menhirLib ];
  propagatedBuildInputs = [
    flocq
    MenhirLib
  ];

  postPatch = ''
    substituteInPlace ./configure \
      --replace \$\{toolprefix\}ar 'ar' \
      --replace '{toolprefix}gcc' '{toolprefix}cc'
  '';

  configurePhase = ''
    ./configure -clightgen \
    -prefix $out \
    -coqdevdir $out/lib/coq/${coq.coq-version}/user-contrib/compcert \
    -toolprefix ${tools}/bin/ \
    -use-external-Flocq \
    -use-external-MenhirLib \
    ${target} \
  ''; # do NOT remove the above "\", this must NOT end with a newline (c.f. below)

  installFlags = [ ]; # trust ./configure

  postInstall = ''
    # wrap ccomp to undefine _FORTIFY_SOURCE; ccomp invokes cc1 which sets
    # _FORTIFY_SOURCE=2 by default, but undefines __GNUC__ (as it should),
    # which causes a warning in libc. this suppresses it.
    for x in ccomp clightgen; do
      wrapProgram $out/bin/$x --add-flags "-U_FORTIFY_SOURCE"
    done
  '';

  meta = {
    description = "Formally verified C compiler";
    homepage = "https://compcert.org";
    license = lib.licenses.inria-compcert;
    platforms = builtins.attrNames targets;
  };
}
