using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class PowerCompactnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/PowerCompactness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic width turns a verbal subgroup into a closed compact image.",
        H("PowerCompactness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("powerproduct"),
                DeclarationHandle.Create(Prefix + "powerProduct"),
                H("Ordered products of powers"),
                StatementSource.FromAuthor(Disp(Eqn(Prod(), C("OrderedProduct", C("Fin", V("w")), Seq(V("i"), Sp, Mapsto, Sp, Pow(C("a", V("i")), V("m"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product follows the order on Fin w. It contains exactly w factors of the form a(i) to the mth power. An empty product is one; factors are never permuted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("haspowerwidth"),
                DeclarationHandle.Create(Prefix + "HasPowerWidth"),
                H("Algebraic power width"),
                StatementSource.FromAuthor(Disp(Seq(C("HasPowerWidth", G(), V("m"), V("w")), Sp, Iff, Sp, All("g", G(), Implies(Member(V("g"), P()), Ex("a", C("Functions", C("Fin", V("w")), G()), Eqn(Prod(), V("g")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every element of the generated power subgroup must be represented by an ordered product of exactly w powers. Padding uses identity elements. This is an algebraic proposition, with no openness assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powerproduct-mem"),
                DeclarationHandle.Create(Prefix + "powerProduct_mem"),
                H("Product membership"),
                StatementSource.FromAuthor(Disp(All("a", C("Functions", C("Fin", V("w")), G()), Member(Prod(), P())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An ordered product of powers belongs to their generated subgroup in any group, including width zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("range-powerproduct-eq"),
                DeclarationHandle.Create(Prefix + "range_powerProduct_eq"),
                H("The power-product image"),
                StatementSource.FromAuthor(Disp(Implies(C("HasPowerWidth", G(), V("m"), V("w")), Eqn(C("Range", C("powerProduct", V("m"), V("w"))), P())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the width proposition, the power subgroup equals the image of the ordered product map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-powerproduct"),
                DeclarationHandle.Create(Prefix + "continuous_powerProduct"),
                H("Continuity of ordered products"),
                StatementSource.FromAuthor(Disp(Implies(C("TopologicalGroup", G()), C("Continuous", C("powerProduct", V("m"), V("w")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a topological group the finite ordered product of coordinatewise powers is continuous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isclosed-powersubgroup-of-width"),
                DeclarationHandle.Create(Prefix + "isClosed_powerSubgroup_of_width"),
                H("Compact image gives closedness"),
                StatementSource.FromAuthor(Disp(Implies(C("CompactHausdorffTopologicalGroup", G()), Implies(C("HasPowerWidth", G(), V("m"), V("w")), C("IsClosed", P()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a compact Hausdorff topological group, bounded algebraic width makes the power subgroup a compact finite-product image and hence a closed set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isopen-powersubgroup-of-closed-finite"),
                DeclarationHandle.Create(Prefix + "isOpen_powerSubgroup_of_closed_finite"),
                H("Closed finite quotient gives openness"),
                StatementSource.FromAuthor(Disp(Implies(C("TopologicalGroup", G()), Implies(And(C("IsClosed", P()), C("Finite", C("Quotient", G(), P()))), C("IsOpen", P()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a topological group, a closed power subgroup with an explicitly finite abstract quotient is open, by the closed finite-index subgroup theorem."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula G() => V("G");
    private static Formula P() => C("powerSubgroup", G(), V("m"));
    private static Formula Prod() => C("powerProduct", V("m"), V("w"), V("a"));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, Open, V(n), Colon, Sp, t, Close, Comma, Sp, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        Seq(Exists, Sp, Open, V(n), Colon, Sp, t, Close, Comma, Sp, b);
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
}
