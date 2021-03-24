{
  description = "Scheme interpreter based on R5RS denotational semantics";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    utils.url = "github:numtide/flake-utils";
    inclusive.url = "github:input-output-hk/nix-inclusive";
  };

  outputs = { self, nixpkgs, utils, inclusive }:
    utils.lib.eachDefaultSystem (system:
      with import nixpkgs { inherit system; }; {
        defaultPackage = haskellPackages.callPackage ({ mkDerivation, base, containers, lib, mtl, parsec, transformers }:
          mkDerivation {
            pname = "r5rs-denot";
            version = "0.1.0.0";
            src = inclusive.lib.inclusive ./. [
              ./src
              ./r5rs-denot.cabal
              ./Setup.hs
              ./LICENSE
            ];
            isLibrary = false;
            isExecutable = true;
            executableHaskellDepends = [
              base containers mtl parsec transformers
            ];
            license = lib.licenses.mit;
          }) {};
      }
    );
}
