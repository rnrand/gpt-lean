(*
Chapter 9
Graphs
Graphs are a very general class of object, used to formalize a wide variety
of practical problems in computer science. In this chapter, we’ll see the basics
of (finite) undirected graphs, including graph isomorphism and connectivity.
*)

Require Import Coq.Sets.Ensembles.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Section Graphs.

(* A graph consists of a set of nodes V and a set of edges E. We'll sometimes
refer to the graph as a pair of sets (V, E). Each edge in E joins two nodes
in V. Two nodes connected by an edge are called neighbors or adjacent. *)

Variable Vertex : Type.
Variable Edge : Ensemble (Vertex * Vertex).

(*
For example, here is a graph in which the nodes are Illinois cities and the
edges are roads joining them:

Chicago - Springfield
Springfield - Bloomington
Bloomington - Urbana
Urbana - Danville
Danville - Decatur
*)

(*
A graph edge can be traversed in both directions, as in this street example,
i.e. the edges are undirected.
When discussing relations earlier, we used directed graphs, in
which each edge had a specific direction. Unless we explicitly state otherwise,
a "graph" will always be undirected.
*)

(* Degrees *)

(* The degree of a node v, written deg(v) is the number of edges which have v as
an endpoint. Self-loops, if you are allowing them, count twice.
*)

(* Manual fix -- commented out. Does it expect nat_of_P to be nat_of_Prop? That doesn't make sense.
   Also, vertex is a Type not an ensemble. 
Require Import Coq.PArith.BinPos. (* Manual - added library *)
Require Import Coq.Sets.Finite_sets. (* Manual - added library *)

Definition degree (v : Vertex) : nat :=
  nat_of_P (cardinal _ (Ensembles.Add _ (Singleton _ v) Empty_set)). (* Manual fix -- EnsembleAdd -> Ensembles.Add *)
*)
Definition degree (v : Vertex) : nat.
Admitted.

(* Manual fix -- commented out.
(* Handshaking Theorem *)
Lemma Handshaking_Theorem: 
  forall G : Ensemble Vertex,
  exists E : Ensemble (Vertex * Vertex),
  (forall v : Vertex, In _ G v -> degree v mod 2 = 0) ->
  exists l : list Vertex, NoDup l /\ forall x, In _ G x <-> In _ (Ensembles.Add _ (Singleton _ x) Empty_set) x.
Proof.
  (* This proof isn't quite straightforward to unwrap here, 
     so we leave it as an exercise/example for the reader. *)
  Admitted.
 *)

(* A graph is called a simple graph if it has neither multiple edges nor loop edges.
Unless we explicitly state otherwise, a "graph" will always be a simple graph.
*)

(* Complete Graphs *)

(* Several special types of graphs are useful as examples. First,
the complete graph on n nodes (shorthand name Kn), is a graph with n nodes in 
which every node is connected to every other node.
*)

(* Number of edges in a complete graph of n vertices *)
Definition complete_edges (n : nat) : nat :=
  n * (n - 1) / 2.

(*
For example, K3 would have 3 nodes and 3 edges.
*)

(* Cycle graphs and wheels *)

(* 
Cycle graph Cn is the graph with n nodes and edges connecting vi to vi+1,
plus an additional edge from vn to v1.
*)

Definition cycle_edge_set (n : nat) : Ensemble (Vertex * Vertex) :=
  (* This is a conceptual representation. A full definition would require a more detailed coding approach,
     perhaps mapping each integer to a pair of vertices and constructing the ensemble from there.
   *)
  Full_set _.

(*
Note: A complete formalization of graphs would require us to more precisely 
define vertices, edges, and other concepts in terms of Coq's type system 
and provide detailed proof structures for concepts like graph isomorphism, 
connectivity, etc. This snippet provides a light structure around these ideas.
*)

End Graphs.
