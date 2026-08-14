{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "inclogic";

  ## Indicate the relative location of your _CoqProject
  coqproject = "_CoqProject";

  ## Extra packages to have around.  The toolbox already puts `coq-lsp` and
  ## the Coq-era `vscoq-language-server` in the shell; this adds the Rocq one,
  ## which is what the VsRocq editor extension talks to.
  buildInputs = [ "vsrocq-language-server" ];

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  ## "9.2" is the latest stable Rocq release; the older bundles are kept for
  ## compatibility testing.
  default-bundle = "9.2";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  ##
  ## The development is Rocq-only (it uses the `Stdlib` prefix), so the
  ## bundles only mention `rocqPackages`: the toolbox then skips the
  ## `coqPackages` compatibility shim entirely.

  bundles."9.2" = {
    rocqPackages = {
      rocq-core.override.version = "9.2";
      mathcomp.override.version = "2.6.0";
      mathcomp-finmap.override.version = "2.2.4";
      ## 1.9.0 is the first release supporting Rocq 9.2; nixpkgs does not know
      ## it yet, hence `.nix/rocq-overlays/relation-algebra`.
      relation-algebra.override.version = "1.9.0";
    };
    coqPackages.coq.override.version = "9.2";
  };

  bundles."9.0" = {
    rocqPackages = {
      rocq-core.override.version = "9.0";
      mathcomp.override.version = "2.5.0";
      mathcomp-finmap.override.version = "2.2.2";
      relation-algebra.override.version = "1.8.0";
    };
    ## Nothing here depends on the Coq compatibility layer, but the `nix-shell`
    ## pulls `coq-lsp`/`vscoq-language-server` out of `coqPackages`; keeping
    ## `coq` in step with `rocq-core` avoids rebuilding them from source.
    coqPackages.coq.override.version = "9.0";
  };

  bundles."9.1" = {
    rocqPackages = {
      rocq-core.override.version = "9.1";
      mathcomp.override.version = "2.5.0";
      mathcomp-finmap.override.version = "2.2.2";
      relation-algebra.override.version = "1.8.0";
    };
    coqPackages.coq.override.version = "9.1";
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
