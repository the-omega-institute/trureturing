using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class NatPresburgerSolverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive Option contracts cover fixed parameters and all-coordinate solving.", H("Executable native decisions and Option solutions"),
        Blocks(Paragraph(Text("BF(m,n) is the native finite-context bounded formula type, and NatTuple(r)=Fin r->Nat. test decides satisfaction for a complete free/bound valuation. solveBounded fixes the free valuation and returns Option(NatTuple(n)); solveAll returns Option(NatTuple(m+n)). Every statement below keeps the original native Realize semantics.")),
            Paragraph(Text("Existential closure, relabeling and witness extraction reuse the supplied native exs, relabel and Encodable.choose implementations. There is no new custom tuple enumeration or quantifier-elimination procedure. The search predicate is the executable Bool test. Proof-only classical reasoning does not replace the computational decision path.")),
            Paragraph(Text("These interfaces are useful for extracting finite natural assignments and for deciding formulas with arbitrary alternation and nested negation. They establish executable Lean definitions and exact semantic contracts. They do not establish a recursion-theoretic Computable theorem, a complexity estimate, or a uniform practical runtime bound. Encodable search cost depends on the tuple encoding; semantic correctness alone is not a measurement of runtime completion.")),
            Describe.Lean(DescribeId.Create("test-correct"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.test_correct"),
            H("Boolean native decision"), StatementSource.FromAuthor(F.Disp(B(A("xs",Call("NatTuple", V("n")),I(E(Call("test",V("p"),V("v"),V("xs")),V("true")),Call("Realize", V("p"), V("v"), V("xs"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("test calls the upstream integer decideHolds on compile(p) and environment(v,xs). Its contract composes the upstream Bool equivalence with compile_correct. realizeDecidable branches on the computed Bool; it does not use a classical proposition decision instance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-bounded-sound"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_bounded_sound"),
            H("A returned bound tuple satisfies the native formula"), StatementSource.FromAuthor(F.Disp(B(A("xs",Call("NatTuple", V("n")),R(E(Call("solveBounded",V("p"),V("v")),Call("some",V("xs"))),Call("Realize", V("p"), V("v"), V("xs"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("solveBounded first tests native existential closure p.exs at the empty bound valuation, using the supplied realize_exs equivalence. Only in the positive branch does Encodable.choose select a finite tuple satisfying test=true; test_correct proves its original native satisfaction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-bounded-exists-some-iff"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_bounded_exists_some_iff"),
            H("Returning some is equivalent to existence"), StatementSource.FromAuthor(F.Disp(B(I(X("xs",Call("NatTuple", V("n")),E(Call("solveBounded",V("p"),V("v")),Call("some",V("xs")))),X("xs",Call("NatTuple", V("n")),Call("Realize", V("p"), V("v"), V("xs"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The right-to-left implication constructs the positive solver branch from any satisfying tuple. The left-to-right implication uses returned-some soundness. The statement quantifies the returned tuple existentially; it does not say that every satisfying tuple is the chosen tuple."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-bounded-none-iff"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_bounded_none_iff"),
            H("None exactly means no satisfying bound tuple"), StatementSource.FromAuthor(F.Disp(B(I(E(Call("solveBounded",V("p"),V("v")),V("none")),N(X("xs",Call("NatTuple", V("n")),Call("Realize", V("p"), V("v"), V("xs")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Option case analysis converts the existence-of-some contract into this exact failure contract. Fin n->Nat has its supplied Encodable instance even when n=0; its empty function is the unique zero-dimensional tuple."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-all-sound"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_all_sound"),
            H("Returned coordinates split into the original free and bound parts"), StatementSource.FromAuthor(F.Disp(U(A("w",Call("NatTuple",Add(V("m"),V("n"))),R(E(Call("solveAll",V("p")),Call("some",V("w"))),S(V("w"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("solveAll directly applies native BoundedFormula.relabel with Sum.inr, promoting the original free coordinates into the bound context before solveBounded. free(w,m,n)=w o Fin.castAdd n reads indices 0 through m-1. bound(w,m,n)=w o Fin.natAdd m reads indices m through m+n-1. Native realize_relabel proves the original coordinate split."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-all-exists-some-iff"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_all_exists_some_iff"),
            H("Some exists exactly when the original formula has a full tuple"), StatementSource.FromAuthor(F.Disp(U(I(X("w",Call("NatTuple",Add(V("m"),V("n"))),E(Call("solveAll",V("p")),Call("some",V("w")))),X("w",Call("NatTuple",Add(V("m"),V("n"))),S(V("w"))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("This is existence over the full Fin(m+n) tuple. Both quantifiers refer to the same coordinate convention. Multiple solutions are allowed and a successful solver chooses one of them."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("solve-all-none-iff"),
            DeclarationHandle.Create("D5/S0/Computability/NatPresburgerSolver.solve_all_none_iff"),
            H("None exactly means no full native tuple"), StatementSource.FromAuthor(F.Disp(U(I(E(Call("solveAll",V("p")),V("none")),N(X("w",Call("NatTuple",Add(V("m"),V("n"))),S(V("w")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("The fixed-parameter none contract transports through native realize_relabel. With m=0 only the bound part remains; with n=0 only the promoted free part remains; with m=n=0 both parts are the empty function."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/NatPresburgerCompiler")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerDecision"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula X(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
    private static Formula I(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Iff, F.Sp, F.Open, right, F.Close);
    private static Formula R(Formula left, Formula right) => F.Seq(F.Open, left, F.Close, F.Sp, F.Implies, F.Sp, F.Open, right, F.Close);
    private static Formula N(Formula body) => F.Seq(F.Neg, F.Sp, F.Open, body, F.Close);
    private static Formula U(Formula body) => A("m", V("Nat"), A("n", V("Nat"),
        A("p", Call("BF", V("m"), V("n")), body)));
    private static Formula B(Formula body) => U(A("v", Call("NatTuple", V("m")), body));
    private static Formula S(Formula w) => Call("Realize", V("p"),
        Call("free", w, V("m"), V("n")), Call("bound", w, V("m"), V("n")));
}
