using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntrySpectralGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntrySpectralGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The single-entry secular root in free-mode coordinates.",
        H("Rank-one spectral extension"),
        Blocks(
            Describe.Lean(DescribeId.Create("single-entry-mode-negative-generator"),
                DeclarationHandle.Create(Prefix + "modeNegativeGenerator"), H("Mode matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index set is Option(Finset(I)), with none the attached repressed coordinate. Writing H for the sum of all subset coordinates, the matrix B acts by (Bx)(none)=h x(none)-e H and (Bx)(S)=s(S)x(S)+W(S)(e H-h x(none)). Here e=eta and h=theta. These are free-mode coordinates; the matrix is not defined by assuming its eigenvalues or its secular equation. A product change of basis is required to identify B with the actual configuration generator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-secular-least-mode-eigenvalue"),
                DeclarationHandle.Create(Prefix + "secular_root_least_mode_eigenvalue"), H("Least positive mode eigenvalue"),
                StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonempty finite site family and positive rates, there is a positive scalar l below every site rate, satisfying F(l)=0, with a nonzero vector x satisfying Bx=l x. Every positive real m admitting such a nonzero eigenvector satisfies l<=m. The proof first eliminates the subset coordinates: x(S)=l W(S)x(none)/(s(S)-l). If x(none)=0, every coordinate is zero, contradicting the eigenvector premise. Summing the solved coordinates gives F(l)=0. Conversely F(l)=0 produces an eigenvector by x(none)=1 and the displayed subset formula. The earlier unique-root theorem then excludes every smaller positive eigenvalue. This theorem does not discharge the product change of basis between B and the configuration generator, and it does not assert a slow-tail coefficient."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Positive(Formula v) => Rel(D(0), FormulaRelationOperator.LessThan, v);
    private static Formula Matrix() => Call("modeNegativeGenerator", F.Id("a"), F.Id("b"), F.Id("e"), F.Id("h"));
    private static Formula Vector() => Seq(Call("Option", Call("Finset", F.Id("I"))), Sp, To, Sp, R());
    private static Formula Eigen(string v, Formula l) => Ex(v, Vector(), And(
        Rel(F.Id(v), FormulaRelationOperator.NotEqual, D(0)),
        Rel(Call("mulVec", Matrix(), F.Id(v)), FormulaRelationOperator.Equal, Call("smul", l, F.Id(v)))));
    private static Formula Formula()
    {
        var l = F.Id("l"); var m = F.Id("m"); var i = F.Id("i");
        var result = Ex("l", R(), And(Positive(l), And(
            All("i", F.Id("I"), Rel(l, FormulaRelationOperator.LessThan, Call("siteRate", F.Id("a"), F.Id("b"), i))), And(
            Rel(Call("secular", F.Id("a"), F.Id("b"), F.Id("e"), F.Id("h"), l), FormulaRelationOperator.Equal, D(0)), And(
            Eigen("x", l), All("m", R(), Imp(Positive(m), Imp(Eigen("y", m), Rel(l, FormulaRelationOperator.LessThanOrEqual, m)))))))));
        var rates = And(All("i", F.Id("I"), Positive(Call("a", i))), And(
            All("i", F.Id("I"), Positive(Call("b", i))), And(Positive(F.Id("e")), Positive(F.Id("h")))));
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var body = All("a", fn, All("b", fn, All("e", R(), All("h", R(), Imp(rates, result)))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", F.Id("I")), CloseBracket, Sp, body)));
    }
}
