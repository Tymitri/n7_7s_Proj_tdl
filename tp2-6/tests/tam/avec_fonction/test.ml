open Rat
open Compilateur

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../../../../tests/runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/tam/avec_fonction/fichiersRat/"

(**********)
(*  TESTS *)
(**********)


(* requires ppx_expect in jbuild, and `opam install ppx_expect` *)
let%expect_test "testfun1" =
  runtam (pathFichiersRat^"testfun1.rat");
  [%expect{| 1 |}]

let%expect_test "testfun2" =
  runtam (pathFichiersRat^"testfun2.rat");
  [%expect{| 7 |}]

let%expect_test "testfun3" =
  runtam (pathFichiersRat^"testfun3.rat");
  [%expect{| 10 |}]

let%expect_test "testfun4" =
  runtam (pathFichiersRat^"testfun4.rat");
  [%expect{| 10 |}]

let%expect_test "testfun5" =
  runtam (pathFichiersRat^"testfun5.rat");
  [%expect{| |}]

let%expect_test "testfun6" =
  runtam (pathFichiersRat^"testfun6.rat");
  [%expect{|truetrue|}]

let%expect_test "testfuns" =
  runtam (pathFichiersRat^"testfuns.rat");
  [%expect{| 28 |}]

let%expect_test "factrec" =
  runtam (pathFichiersRat^"factrec.rat");
  [%expect{| 120 |}]

let%expect_test "testPointeur1" =
  runtam (pathFichiersRat^"testPointeur1.rat");
  [%expect{| 3 |}]

  let%expect_test "testPointeur2" =
  runtam (pathFichiersRat^"testPointeur2.rat");
  [%expect{| 3 |}]

  let%expect_test "testPointeur3" =
  runtam (pathFichiersRat^"testPointeur3.rat");
  [%expect{| 3 |}]

let%expect_test "testternaire1" =
  runtam (pathFichiersRat^"testternaire1.rat");
  [%expect{| true |}]

let%expect_test "testBoucle1" =
  runtam (pathFichiersRat^"testBoucle1.rat");
  [%expect{| 012345678910 |}]

let%expect_test "testBoucle2" =
  runtam (pathFichiersRat^"testBoucle2.rat");
  [%expect{| 1266645 |}]

let%expect_test "testBoucle3" =
  runtam (pathFichiersRat^"testBoucle3.rat");
  [%expect{| 240 |}]

let%expect_test "testBoucle4" =
  runtam (pathFichiersRat^"testBoucle4.rat");
  [%expect{| 0123456789101112131415161718192021222301234567891011121314151617181920212223 |}]

let%expect_test "testBoucle5" =
  runtam (pathFichiersRat^"testBoucle5.rat");
  [%expect{| 0123456789101112131415161718192021222301234567891011121314151617181920212223 |}]

let%expect_test "testBoucle6" =
  runtam (pathFichiersRat^"testBoucle6.rat");
  [%expect{| 01234567891011121314151617181920212223 |}]

let%expect_test "testBoucle7" =
  runtam (pathFichiersRat^"testBoucle7.rat");
  [%expect{| 1010 |}]

let%expect_test "testBoucle8" =
  runtam (pathFichiersRat^"testBoucle8.rat");
  [%expect{| 0101010101888 |}]