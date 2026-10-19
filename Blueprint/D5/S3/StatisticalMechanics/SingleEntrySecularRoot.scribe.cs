using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntrySecularRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntrySecularRoot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar secular equation for a finite single-entry inhibition network.",
        H("A unique root below all free relaxation rates"),
        Blocks(
            Node("siteRate", "Free site rate",
                "For positive binding and unbinding rates a and b, the free relaxation rate is s(i) = a(i) + b(i).", DescribeRole.Definition),
            Node("occupancy", "Free occupancy",
                "The free equilibrium occupancy is q(i) = a(i)/s(i).", DescribeRole.Definition),
            Node("subsetRate", "Subset rate",
                "For a subset S of sites, s(S) is the sum of s(i) over S.", DescribeRole.Definition),
            Node("modeWeight", "Subset weight",
                "The empty-configuration spectral weight W(S) is the product over all sites of q(i) on S and 1-q(i) off S. Positivity follows from a(i),b(i)>0.", DescribeRole.Definition),
            Node("secular", "Secular function",
                "With entry rate e and return rate h, F(x) = h + e W(empty) - x - e x times the sum of W(S)/(s(S)-x) over nonempty S. The symbols e and h denote eta and theta respectively.", DescribeRole.Definition),
            Node("secularSlope", "Pole-weight slope",
                "The independent pole-weight expression is -1-e times the sum of W(S)s(S)/(s(S)-x)^2 over nonempty subsets. The theorem identifies it with the derivative of F throughout the nonnegative pre-pole interval and proves it strictly negative.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-weight-pos"),
                DeclarationHandle.Create(Prefix + "weight_pos"), H("Positive product-mode weights"),
                StatementSource.FromAuthor(WeightFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite family of strictly positive binding and unbinding rates and every subset S, the empty-configuration mode weight W(S) is strictly positive. Each factor is q(i)>0 on S or 1-q(i)>0 off S."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-entry-secular-unique-root"),
                DeclarationHandle.Create(Prefix + "secular_unique_root"), H("Unique scalar root"),
                StatementSource.FromAuthor(RootFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every nonempty finite family of positive rates has exactly one positive root below each free site rate. Let m be the minimum site rate and choose a singleton mode j with s(j)=m. Put C=h+e W(empty) and z=m C/(C+e W(j)). Then 0<z<m, the j term alone contributes C to e z times the resolvent sum, and F(z)<=-z<0. All other terms are nonnegative. Continuity and F(0)=C>0 give existence; strict decrease gives uniqueness. Differentiating each x W(S)/(s(S)-x) gives W(S)s(S)/(s(S)-x)^2, proving the stated slope and its strict negativity. This conclusion concerns the scalar equation. Identification with the full generator's smallest positive eigenvalue requires a separate spectral argument."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("single-entry-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
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
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Exists(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Positive(Formula x) => Rel(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula RootAt(Formula x)
    {
        Formula a = F.Id("a"), b = F.Id("b"), e = F.Id("e"), h = F.Id("h");
        return And(Positive(x), And(All("i", F.Id("I"),
            Rel(x, FormulaRelationOperator.LessThan, Call("siteRate", a, b, F.Id("i")))),
            Rel(Call("secular", a, b, e, h, x), FormulaRelationOperator.Equal, D(0))));
    }
    private static Formula WeightFormula()
    {
        var fn = Seq(F.Id("I"), Sp, To, Sp, R());
        var premise = And(All("i", F.Id("I"), Positive(Call("a", F.Id("i")))),
            All("i", F.Id("I"), Positive(Call("b", F.Id("i")))));
        var body = All("a", fn, All("b", fn, Imp(premise,
            All("S", Call("Finset", F.Id("I")), Positive(Call("modeWeight", F.Id("a"), F.Id("b"), F.Id("S")))))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp, body)));
    }
    private static Formula RootFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y");
        Formula root = Exists("x", R(), And(RootAt(x), All("y", R(),
            Imp(RootAt(y), Rel(y, FormulaRelationOperator.Equal, x)))));
        Formula positiveRates = And(All("i", F.Id("I"), Positive(Call("a", F.Id("i")))),
            And(All("i", F.Id("I"), Positive(Call("b", F.Id("i")))),
                And(Positive(F.Id("e")), Positive(F.Id("h")))));
        Formula fn = Seq(F.Id("I"), Sp, To, Sp, R());
        Formula v = F.Id("v");
        Formula prePole = And(Rel(D(0), FormulaRelationOperator.LessThanOrEqual, v),
            All("i", F.Id("I"), Rel(v, FormulaRelationOperator.LessThan,
                Call("siteRate", F.Id("a"), F.Id("b"), F.Id("i")))));
        Formula slope = Call("secularSlope", F.Id("a"), F.Id("b"), F.Id("e"), v);
        Formula derivative = All("v", R(), Imp(prePole, And(
            Call("HasDerivAt", Call("secular", F.Id("a"), F.Id("b"), F.Id("e"), F.Id("h")), slope, v),
            Rel(slope, FormulaRelationOperator.LessThan, D(0)))));
        root = And(root, derivative);
        Formula body = All("a", fn, All("b", fn, All("e", R(), All("h", R(), Imp(positiveRates, root)))));
        return Disp(All("I", F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", F.Id("I")), CloseBracket, Sp, body)));
    }
}
