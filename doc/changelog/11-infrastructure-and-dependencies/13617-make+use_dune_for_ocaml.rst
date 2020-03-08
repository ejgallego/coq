- **Changed:**
  Coq's OCaml parts and tools [coq-core] are now built using Dune.
  The main user-facing change is that Dune >= 2.5 is now required to
  build Coq. For developers and plugin authors, see the entry in
  doc/dev/changes.md
  - the following makefile targets have been removed: byte install-byte
  - Bugs fixed: # , # , #
  (`#13617 <https://github.com/coq/coq/pull/13617>`_,
  by Emilio Jesus Gallego Arias).
