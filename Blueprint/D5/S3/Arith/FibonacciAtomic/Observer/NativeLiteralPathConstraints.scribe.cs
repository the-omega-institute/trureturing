using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeLiteralPathConstraintsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeLiteralPathConstraints", H("Finite native constraints for literal navigation"), Blocks(
            Def("Atom", "Native labels and tree names", "A term leaf is a native alpha or beta label, an original-source epoch coordinate, or an auxiliary tree name. Term is the free ordered binary tree on these atoms. The function label selects a native leaf, original selects an epoch coordinate, and auxiliary selects a bound tree name."),
            Def("Term", "Finite ordered constructor terms", "Terms contain only ordered pairs and the three kinds of leaf names. All occurrences of original refer to the same tree u. The natural function e assigns the substitution exponent to each coordinate; coordinates have no common upper bound."),
            Def("label", "Native labelled leaves", "True is alpha and false is beta. Labels are literal finite constructor terms."),
            Def("original", "One shared original source", "An original coordinate i denotes the iterate of the same u at exponent e(i). It does not denote a separately chosen source."),
            Def("auxiliary", "Auxiliary tree names", "Auxiliary indices refer to the current existential tree environment."),
            Def("value", "Term interpretation", "value u e x interprets labels and ordered pairs literally, original i as substitution iterated e(i) times on u, and auxiliary i as x(i). No source replacement occurs in this interpretation."),
            Def("push", "Opening an existential tree binder", "A new bound tree has index zero. Every previous auxiliary tree moves to its successor index."),
            Def("lift", "Preserving names under a tree binder", "lift increments auxiliary indices, preserves original-source coordinates and labels, and commutes with ordered pairs."),
            Def("Formula", "Finite native formula grammar", "The grammar has falsehood, constructor equality, binary conjunction, binary disjunction and existential tree quantification. It contains no Read predicate, variable address, source oracle or program predicate. Its satisfaction relation Holds is Formula.Holds with the formula argument last. Existential tree quantification ranges over actual finite native trees, using push for its environment; the epoch environment is retained through every tree quantifier."),
            Def("pairStep", "Actual ordered child constraints", "Descent binds the two ordered children and equates their pair to the entire current term. One child is selected by the next literal address bit, while the other remains an existential sibling."),
            Def("compile", "Four-reply literal navigation", "At the root, alpha and beta require their labelled leaves; branch requires two children; absent is false. At a nonempty word, a present reply requires pair descent. Absence permits either labelled leaf at the current strict prefix or recursive descent through an actual pair. Thus an absent endpoint is never assigned a default tree."),
            Describe.Lean(DescribeId.Create("native-literal-path-compile-exact"),
                DeclarationHandle.Create(Prefix + "compile_exact"), H("Exact native navigation constraints"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original finite tree, epoch environment, auxiliary environment, literal finite address, reply and term, satisfaction of the compiled formula is equivalent to the actual four-valued readout of that interpreted term. This includes the empty address and all four replies.")),
                    Paragraph(Text("Induction follows the literal address. A pair equation fixes both actual children and preserves the full current tree; the recursive formula follows the selected child. Every absence alternative ends at a labelled leaf on a strict prefix. The auxiliary trees therefore describe subtrees of the same actual interpreted tree in both directions.")),
                    Paragraph(Text("The construction is finite and structurally recursive. The statement is an extensional semantic equivalence; it does not assert a partial-recursive encoding theorem for the whole formula generator or an enumeration theorem for observer programs."))
                ), DescribeRole.Theorem)
        )));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-literal-path-" + name.Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Statement()
    {
        Formula lhs = Call("Holds", V("u"), V("e"), V("x"),
            Call("compile", V("p"), V("y"), V("V")));
        Formula rhs = EqOf(Call("readout", V("p"),
            Call("value", V("u"), V("e"), V("x"), V("V"))), V("y"));
        Formula f = IffOf(lhs, rhs);
        f = All("V", V("Term"), f);
        f = All("y", V("Reply"), f);
        f = All("p", V("Address"), f);
        f = All("x", Arr(V("Nat"), V("Source")), f);
        f = All("e", Arr(V("Nat"), V("Nat")), f);
        return All("u", V("Source"), f);
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. xs]);
    private static Formula Arr(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
