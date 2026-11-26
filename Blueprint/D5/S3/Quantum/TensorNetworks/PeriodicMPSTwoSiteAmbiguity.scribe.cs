using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSTwoSiteAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-site phase ambiguity for actual periodic binary matrix product states.",
        H("Actual periodic two-site collisions"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-mps-raw-two"), DeclarationHandle.Create(Module + ".rawTwo"),
                H("Raw two-site reduced density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The raw Gram is the two-site amplitude flattening times its conjugate transpose."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("periodic-mps-actual-two-site-ambiguity"),
                DeclarationHandle.Create(Module + ".actual_two_site_ambiguity"),
                H("Rank-four collisions at every ring length at least four"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The target pair has diagonal zero matrix diag(1,i/2) and a one matrix exchanging the virtual basis vectors. Its length-two products span the full bond matrix algebra, which gives rank four at every ring length r+4.")),
                    Paragraph(Text("Parity separates the even and odd prefix blocks of the two-site Gram. Reversing the suffix interchanges the odd prefixes, so the odd off-diagonal entry is real. Entrywise conjugation of the pair and one unit phase on the one symbol preserve the entire Gram. The phase is chosen using the even off-diagonal entry.")),
                    Paragraph(Text("Two selected words contain exactly two ones and differ in their separation. Their amplitudes have a nonreal projective ratio, so conjugation changes the full state up to every complex scalar despite applying the same phase at both words. Existing three-site recovery then distinguishes the two actual states."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = Id("r");
        var a = Id("A");
        var b = Id("B");
        var c = Id("c");
        var n = new Formula.Binary(r, FormulaBinaryOperator.Add, D(4));
        var rank = Eq(Call("rank", Call("twoFlattening", a, r)), D(4));
        var raw = Eq(Call("rawTwo", b, r), Call("rawTwo", a, r));
        var nonphase = All("c", Id("Complex"), Ne(Call("gamma", b, n, D(1)),
            Call("smul", c, Call("gamma", a, n, D(1)))));
        var three = Ne(Call("rawThree", b, r), Call("rawThree", a, r));
        var core = new Formula.TypeArrow(Call("Fin", D(2)), Id("Bond"));
        return All("r", Id("Nat"), Some("A", core, Some("B", core, And(rank, And(raw, And(nonphase, three))))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
