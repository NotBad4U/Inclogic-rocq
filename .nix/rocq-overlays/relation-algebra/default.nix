{
  lib,
  mkRocqDerivation,
  rocq-core,
  stdlib,
  version ? null,
}:

mkRocqDerivation {
  pname = "relation-algebra";
  owner = "damien-pous";

  ## Amended copy of the nixpkgs derivation: as of this writing nixpkgs only
  ## knows 1.8.0 (Rocq 9.0/9.1), so 9.2 is added here.  Drop this overlay once
  ## nixpkgs ships 1.9.0.
  inherit version;
  defaultVersion =
    lib.switch
      [ rocq-core.rocq-version ]
      [
        {
          cases = [ (lib.versions.range "9.2" "9.2") ];
          out = "1.9.0";
        }
        {
          cases = [ (lib.versions.range "9.0" "9.1") ];
          out = "1.8.0";
        }
      ]
      null;

  releaseRev = v: "v${v}";

  release."1.9.0".sha256 = "sha256-VxeyxOhvyZzvJss93IFsoU/k6QinpepFUdIf8PG4V9A=";
  release."1.8.0".sha256 = "sha256-RnY+a57KnStACteaT5dKQoCCH0qp7/W+4qoaApIilj0=";

  propagatedBuildInputs = [
    stdlib
  ];

  dontConfigure = true;

  mlPlugin = true;

  meta = {
    description = "Relation algebra library for Rocq";
    maintainers = with lib.maintainers; [ siraben ];
    license = lib.licenses.gpl3Plus;
    platforms = lib.platforms.unix;
  };
}
