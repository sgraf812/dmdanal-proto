# Largely copy-pasted from
# https://gist.github.com/rpearce/114271b23004c3eb25e55686618786fc
{
  description = "Simple haskell nix flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";

    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { flake-utils, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        config = {};
        overlays = [];
        pkgs = import nixpkgs { inherit config overlays system; };
      in rec {
        devShell = pkgs.haskellPackages.shellFor {
          packages = p: [
          ];

          buildInputs = with pkgs.haskellPackages; [
            haskell-language-server
          ];
        };
      }
    );
}
