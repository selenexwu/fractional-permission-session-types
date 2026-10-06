{ pkgs ? import <nixpkgs> {} }:

with pkgs;

let ocamlPackagesFP = ocamlPackages.overrideScope (self: super: {
      ocaml = (super.ocaml.override { framePointerSupport = true; }).overrideAttrs { doCheck = false; };
}); in

mkShell {
  buildInputs = [
    opam
    ((ocaml.override { framePointerSupport = true; }).overrideAttrs { doCheck = false; })
    dune
    ocamlPackagesFP.findlib
    ocamlPackagesFP.utop
    # ocamlPackagesFP.ocaml-lsp
    ocamlPackagesFP.merlin
    ocamlPackagesFP.ocp-indent
    ocamlPackagesFP.ocamlformat
    ocamlPackagesFP.menhir
    ocamlPackagesFP.core
    ocamlPackagesFP.core_unix
    ocamlPackagesFP.zarith
    ocamlPackagesFP.janeStreet.ppx_let
  ];
}
