(subdir lib
 (executables
  (names pp_big_vect)
  (libraries coq_utest coq.lib))
 
 (rule
  (targets pp_big_vect.ml.log)
  (action (with-accepted-exit-codes 0 (run ./pp_big_vect.exe))))
 
 (alias
  (name runtest) (deps (glob_files *.ml.log))))

(subdir clib
 (executables
  (names unicode_tests
 inteq)
  (libraries coq_utest coq.clib))
 
 (rule
  (targets unicode_tests.ml.log)
  (action (with-accepted-exit-codes 0 (run ./unicode_tests.exe))))
 (rule
  (targets inteq.ml.log)
  (action (with-accepted-exit-codes 0 (run ./inteq.exe))))
 
 (alias
  (name runtest) (deps (glob_files *.ml.log))))

(subdir printing
 (executables
  (names proof_diffs_test)
  (libraries coq_utest coq.printing))
 
 (rule
  (targets proof_diffs_test.ml.log)
  (action (with-accepted-exit-codes 0 (run ./proof_diffs_test.exe))))
 
 (alias
  (name runtest) (deps (glob_files *.ml.log))))

