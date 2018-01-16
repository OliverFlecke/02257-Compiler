#r @"..\packages\FsLexYacc.Runtime.7.0.6\lib\portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10\FsLexYacc.Runtime.dll";
open System
#r @".\bin\Debug\Machine.dll";
#r @".\bin\Debug\VirtualMachine.dll";

#load "AST.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "TypeCheck.fs"
#load "CodeGen.fs"
#load "CodeGenOpt.fs"
#load "Util.fs"
#load "TreeDrawing.fs"
#load "TreeConversion.fs"

open GuardedCommands.Util
open GuardedCommands.Frontend.TypeCheck
open GuardedCommands.Frontend.AST
open GuardedCommands.Backend.CodeGeneration
open Microsoft.FSharp.Text.Lexing
open System.Text
open System.IO

open ParserUtil
open CompilerUtil
open Machine
open VirtualMachine
open Lexer

System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

// let printTokens (lexbuf : LexBuffer<_>) =
//   while not lexbuf.IsPastEndOfStream do
//     printfn "%A" (Lexer.tokenize lexbuf)

// let getBuffer (str:string) = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(str))

// let filename = "tests/" + "Ex0.gc";;

// System.Console.WriteLine ("Starting on " + filename)
// System.Console.WriteLine ("\nParsing...\n")
// let str = File.ReadAllText(filename);;
// // printTokens (getBuffer str)
// let tree = parseFromFile filename;;
// System.Console.WriteLine "Starting type checking..."

// let _ = tcP tree;;
// printfn "Type checking passed"
// printfn ""

// printfn "Code generation starting..."
// go tree;;

// let mapToTestFolder = List.map (fun x -> "tests/" + x)
// Test of programs covered by the first task (Section 3.7):
// List.iter exec <| mapToTestFolder ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;

// // Test of programs covered by the second task (Section 4.3):
// List.iter exec <| mapToTestFolder ["Ex7.gc"; "fact.gc"; "factRec.gc"; "factCBV.gc"];;

// // Test of programs covered by the fourth task (Section 5.4):
// List.iter exec <| mapToTestFolder ["A0.gc"; "A1.gc"; "A2.gc"; "A3.gc"];;

// // Test of programs covered by the fifth task (Section 6.1):
// List.iter exec <| mapToTestFolder ["A4.gc"; "Swap.gc"; "QuickSortV1.gc"];;

// // Test of programs covered by the fifth task (Section 7.4):
// List.iter exec <| mapToTestFolder ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
// List.iter exec ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;


// Drawing trees
open TreeDrawing
open TreeConversion

let file = "tests/" + "QuickSortV1.gc"
let program = parseFromFile file;;

// let tree = Node ("a", ([Node ("b", []); Node ("c", [Node ("e", []); Node ("f", [])]); Node ("d", [Node ("g", []); Node ("h", [])])]))
let tree = convertProgram program
System.Console.WriteLine (string <| design tree)

drawTree tree