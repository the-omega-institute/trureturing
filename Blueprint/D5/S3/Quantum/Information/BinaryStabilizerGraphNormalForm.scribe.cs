using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BinaryStabilizerGraphNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.";
    private static readonly LibraryNoteRef GraphStates =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandennest2004graphical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary quadratic phases describe graph states. A Pauli stabilizer line can be put in this form by single-qubit unitaries.",
        H("Quadratic amplitudes and the graph form of stabilizer states"),
        Blocks(
            Entry("sign-representative", "complex_sign_val", "The sign of the binary representative", SignRepresentative(),
                "The complexSign value is −1 raised to the natural representative of a binary residue.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("amplitude", "graphAmp", "The binary graph amplitude", Amplitude(),
                "Each edge contributes its binary quadratic monomial. The ordered upper-triangular sum is normalExponent; graphAmp is the complexSign value of that exponent, equivalently −1 raised to its natural representative. This definition accepts every binary matrix, without a symmetry or diagonal hypothesis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(GraphStates)),
            Entry("normal-form", "stabilizer_graph_normal_form", "A graph amplitude for every stabilizer line", NormalForm(),
                "The Pauli stabilizers of a nonzero common eigenline span a binary Lagrangian subspace. Coordinate swaps and a diagonal shear express that subspace as the graph of a symmetric matrix with zero diagonal. Hadamard and phase gates implement these transformations, and Pauli signs identify the remaining line with the quadratic amplitude. Taking the inverse gates gives the unitaries U and the scalar c in the displayed equation; SMul.smul denotes scalar action on the amplitude vector.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(GraphStates)))));

    private static Formula SignRepresentative() => All(V("a"), Binary,
        Equal(Call("complexSign", V("a")),
            Pow(Typed(Seq(Minus, D(1)), Complex), Property(V("a"), "val"))));

    private static Formula Amplitude() => All(V("N"), Nat,
        All(Gamma, Matrix(Fin(V("N")), Binary), All(V("x"), Arrow(Fin(V("N")), Fin(D(2))),
            Equal(Call("graphAmp", Gamma, V("x")),
                Pow(Typed(Seq(Minus, D(1)), Complex),
                    Property(Call("normalExponent", Gamma, Typed(V("x"), Arrow(Fin(V("N")), Binary))), "val"))))));

    private static Formula NormalForm() => All(V("N"), Nat,
        All(Psi, Arrow(Arrow(Fin(V("N")), Fin(D(2))), Complex),
            Imp(Call("StabilizedBy", V("pauliSet"), Psi),
                Some(V("U"), Arrow(Fin(V("N")), Matrix(Fin(D(2)), Complex)),
                    Some(Gamma, Matrix(Fin(V("N")), Binary), Some(V("c"), Complex,
                        Conj(Parenthesized(All(V("i"), Fin(V("N")),
                                Seq(Call("U", V("i")), Sp, InMacro, Sp, Call("unitaryGroup", Fin(D(2)), Complex)))),
                            Conj(Property(Gamma, "IsSymm"),
                                Conj(Parenthesized(All(V("i"), Fin(V("N")), Equal(Apply(Gamma, V("i"), V("i")), D(0)))),
                                    Equal(Psi, Qualified("SMul", "smul", V("c"), Parenthesized(
                                        Seq(Call("tensorOp", V("U")), Sp, Star, Underscore, Grp(V("v")), Sp,
                                            Call("graphAmp", Gamma))))))))))))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), provenance,
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Binary => Call("ZMod", D(2));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula index, Formula field) => Call("Matrix", index, index, field);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, bodyGroup(b));
    private static Formula bodyGroup(Formula x) => Parenthesized(x);
    private static Formula Conj(Formula a, Formula b) => Seq(a, Sp, Land, Sp, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Property(Formula x, string property) => Seq(Parenthesized(x), Dot, V(property));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) => Seq(V(owner), Dot, Call(name, args));
    private static Formula Apply(Formula f, params Formula[] args) => Seq(f, Open, Arguments(args), Close);
    private static Formula Arguments(Formula[] args) => Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]);
}
