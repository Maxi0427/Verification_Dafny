// Thanks to Konstantinos Kallas for making this demo!

// We will go through a slightly modified version of the official Dafny tutorial:
//   https://dafny-lang.github.io/dafny/OnlineTutorial/guide
//
// After the lecture I will send a link to this source file `lecture-filled.dfy` and you can look at it in your own pace.

// Feel free to stop me during the demo, ask any questions, or ask me to go faster/slower.

//
// Intro to Dafny
//

// Methods are functions in standard languages, 
//   we have standard programming constructs (ifs, fors, etc).
//
// In addition to those, we have postconditions (`ensures`) that allow specifying
//   what needs to hold after the method finishes executing.
//
// Return values are named so that we can refer to them in postconditions.
method Abs(x: int) returns (y: int)
   ensures 0 <= y
{
   if x < 0 {
      return -x;
   } else {
      return x;
   }
}

// Let's see if our Dafny installation is working by modifying the `ensures` to something that does not hold,
//   e.g., `1 <= y`.


























// Methods can also have multiple return values, and multiple postconditions.
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
   requires 0 < y // Comment this out and see what happens!
   ensures less < x
   ensures x < more
{
   more := x + y;
   less := x - y;
   // comments: are not strictly necessary
}









// Let's now do a mini-exercise. What kind of pre and postconditions would we like to have in a `Max` function?
//   There are many ways to write them.

method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
{
  // fill in the code here
}



















// Let's now try to use `Abs`, a previously defined method, 
//   in another method, and assert something about it.

method Testing()
{
   
}

// What is a reasonable thing to assert here?






















// Dafny cannot prove 1 <= v even though it is true.
//
// This is because Dafny abstracts functions away by their pre and postconditions
//   to simplify verification. This means that it doesn't look inside Abs' definition
//   to verify the assertion, but rather uses the knowledge that it has of Abs' model.
//
// This is a pretty standard scenario when trying to verify software verification, 
//   where we need to strengthen the model by making the postcondition stronger. 

// What postconditions should we add to Abs to be able to prove that `1 <= Abs(5)`?





















// However, our spec now describes exactly the body of the method, which is a bit redundant.
//
// Dafny has a solution for this, and allows us to define mathematical functions 
//   that are not opaque when Dafny verifies.

// During demo: Insert a function for abs

// Let's now try to write the same test to assert something strong about the return value of `abs`.





// Note that functions support recursion and can appear in expressions.
//
// Let's define a function that computes a given fibonaci number
function fib(n: nat): nat
{
   n
}




















// This function would be really slow due to recomputations if implemented as is,
//   so let's implement a fast method, and prove that it is equivalent.
//
// We first need a loop, and then we will see one of the main very important notions of verification, i.e., loop invariants.
//
// Refresher on loop invariants:
//
// Loop invariants hold in the beginning and end of the loop, and therefore are used
//   to model the behavior of a loop. Finding invariants is the hardest part, since we need to "guess" an invariant that both
//   (i) is satisfied at the beginning of the loop
//   (ii) is preserved by the loop
//   (iii) is strong enough to prove what we want after the loop


method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)
{

}






















//
// Arrays
//

// Dafny supports imperative arrays. The only difference with C is that the array has its length in the data structure.

method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
   // Can we write code that satisfies the postcondition?
}






















// If we have time we can also look at this FindMax
method FindMax(a: array<int>) returns (max_i: int)
   requires a.Length > 0
   ensures 0 <= max_i < a.Length
   ensures forall k :: 0 <= k < a.Length ==> a[max_i] >= a[k]
{

}



























// Our postconditions and invariants are starting to grow big
//   (especially when dealing with arrays)
//   and so we would like to abstract away parts of them.
//
// For that, we can use predicates, i.e., boolean functions that can only be used in specifications.

// Let's write a predicate that holds if its input array is sorted.

predicate sorted(a: array<int>)
   reads a // Necessary to give ownership to a predicate (or function) to read/write an array
{
   true
}























// And now to gather everything that we have seen in the lecture already, 
//   let's write the spec for a binary search, and then implement and verify it.
//
// We will go through the whole process, debugging whatever might go wrong etc.
method BinarySearch(a: array<int>, value: int) returns (index: int)
    // During the lecture: Write pre and postconditions
{

}































//
// Allocating arrays
//

// Until now for simplicity we haven't shown any array allocation, but Dafny allows that too with the `new` keyword.

method copy(a: array<int>) returns (b: array<int>)
// Fill in the postconditions please!!!
{

}


























//
// Sequences
//

// I will now give a brief overview of sequences to show how they facilitate verification. 
//   For a more complete reference see: (https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf)

// Let's say we wanted to write a predicate that holds if a slice of the array was sorted

predicate sorted_slice(a: array<int>, start: int, end: int)
{
   true
}

















// yuck

// Sequences can help by allowing for easy slicing and slightly more succint syntax.
//   Also they are immutable meaning that Dafny doesn't need to care about whether they are modified or not.


predicate sorted_seq(a: seq<int>)
{
   true
}









// And let's use it

method test_seq()
{

}
















//
// Auxiliary State
//

// The final thing that one needs to know for the homework is that often 
//   the implementation code is not adequate for dafny to verify postconditions 
//   (especially in the presence of loops).
//
// In addition to the original code and state, there is often need for 
//   extra auxiliary state (variables, arrays) that can help establish a fact that is needed for a postcondition.
//
// An example of such extra state that might be helpful is a data structure that "logs" some important actions
//   that were done in the loop.
//
// This might not make much sense abstractly, but it will be useful for the homework!
























// And finishing with a quote form the official dafny tutorial
//
// ```
//    Even if you do not use Dafny regularly, the idea of writing down exactly 
//    what it is that the code does in a precise way, and using this to prove code correct 
//    is a useful skill. Invariants, pre- and postconditions, and annotations are useful 
//    in debugging code, and also as documentation for future developers. When modifying 
//    or adding to a codebase, they confirm that the guarantees of existing code are not broken. 
//    They also ensure that APIs are used correctly, by formalizing behavior and requirements 
//    and enforcing correct usage. Reasoning from invariants, considering pre- and postconditions, 
//    and writing assertions to check assumptions are all general computer science skills 
//    that will benefit you no matter what language you work in.
// ```
