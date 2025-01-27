## File initially generated by createOverlay
## and then supposedly modified manually.
## Some hints for manual modifications are in the file,
## but the full doc is on nixos / nix packages website:
## https://nixos.org/manual/nixpkgs/stable/#sec-language-coq

{ lib, mkCoqDerivation, which, coq
  ## declare extra dependencies here, to be used in propagateBuildInputs e.g.
  , mathcomp, coq-elpi, hierarchy-builder
  , mathcomp-finmap
  , mathcomp-zify
  , mathcomp-algebra-tactics
  , equations
  , deriving
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "PPND";
  ## you can configure the domain, owner and repository, the default are:
  # owner = "coq-community";
  # domain = "github.com";

  inherit version;
## The `defaultVersion` attribute is important for nixpkgs but can be kept unchanged
## for local usage since it will be ignored locally if
## - this derivation corresponds to the main attribute,
## - or its version is overridden (by a branch, PR, url or path) in `.nix/config.nix`.
  defaultVersion = with versions; switch coq.coq-version [
    ## Example of possible dependencies
    # { case = range "8.13" "8.14"; out = "1.2.0"; }
    ## other predicates are `isLe v`, `isLt v`, `isGe v`, `isGt v`, `isEq v` etc
  ] null;

  ## Declare existing releases
  ## leave sha256 empty at first and then copy paste
  ## the resulting sha given by the error message
  # release."1.1.1".sha256 = "";
  ## if the tag is not exactly the version number you can amend like this
  # release."1.1.1".rev = "v1.1.1";
  ## if a consistent scheme gives the tag from the release number, you can do like this:
  # releaseRev = v: "v${v}";

  ## Add dependencies in here. In particular you can add
  ## - arbitrary nix packages (you need to require them at the beginning of the file)
  ## - Coq packages (require them at the beginning of the file)
  ## - OCaml packages (use `coq.ocamlPackages.xxx`, no need to require them at the beginning of the file)
  propagatedBuildInputs = [ mathcomp coq-elpi hierarchy-builder
    mathcomp-finmap deriving equations
    mathcomp-zify mathcomp-algebra-tactics ]; ## e.g. `= [ mathcomp coq-elpi ]`

  ## Does the package contain OCaml code?
  # mlPlugin = false;

  ## Give some meta data
  ## This is needed for submitting the package to nixpkgs but not required for local use.
  meta = {
    ## Describe your package in one sentence
    # description = "";
    ## Kindly ask one of these people if they want to be an official maintainer.
    ## (You might also consider adding yourself to the list of maintainers)
    # maintainers = with maintainers; [ cohencyril siraben vbgl Zimmi48 ];
    ## Pick a license from
    ## https://github.com/NixOS/nixpkgs/blob/master/lib/licenses.nix
    # license = licenses.mit;
  };
}
