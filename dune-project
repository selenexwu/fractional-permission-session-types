(lang dune 3.6)

(name fracst)

(generate_opam_files)

(using menhir 2.0)

(package
 (name fracst)
 (synopsis "FracST Implementation")
 (authors "Selene Wu" "Ankush Das")
 (depends
  (core (>= v0.17.2))
  (core_unix (>= v0.17.1))
   dune
  (menhir (>= 20260209))
  (ocaml (>= 5.5.1))
  (ppx_let (>= v0.17.1))
  (zarith (>= 1.14))
 )
)
