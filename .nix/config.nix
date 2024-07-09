{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "coqpilotTests";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  default-bundle = "8.19";

  bundles."8.17" = {
    push-branches = [ "master" "main" ];
    coqPackages.hahn.override.version = "master";
  };
  bundles."8.18" = {
    push-branches = [ "**" ];
    coqPackages.coq-lsp.override.version = "0.1.8";
    coqPackages.hahn.override.version = "master";
  };
  bundles."8.19" = {
    coqPackages.coqhammer.override.version = "1.3.2-coq8.19";
    coqPackages.hahn.override.version = "master";
    coqPackages.coq.override.version = "8.19";
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.weakmemory = {};
}
