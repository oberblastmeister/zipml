(lang dune 3.13)

(name zipml)

(generate_opam_files true)

(using menhir 3.0)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name zipml)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  ocaml
  dune
  (core
   (= v0.17.1))
  (ppx_deriving
   (= 5.2.1))
  (ppx_jane
   (= v0.17.0))
  (alcotest
   (= 1.7.0))
  (algaeff
   (= 2.0.0))
  (asai
   (= 0.3.1))
  (bwd
   (= 2.3.0))
  menhir)
 (tags
  (topics "to describe" your project)))
