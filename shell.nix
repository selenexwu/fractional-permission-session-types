{ pkgs ? import <nixpkgs> {} }:

with pkgs;

mkShell {
  buildInputs = [
    opam
    ocaml
    dune
    ocamlPackages.findlib
    ocamlPackages.utop
    ocamlPackages.merlin
    ocamlPackages.ocp-indent
    ocamlPackages.ocamlformat
    ocamlPackages.menhir
    ocamlPackages.core
    ocamlPackages.core_unix
    ocamlPackages.zarith
    ocamlPackages.janeStreet.ppx_let
  ];
}
