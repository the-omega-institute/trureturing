using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ProfiniteQuotientBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/ProfiniteQuotientBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform finite quotient bounds control closed normal quotients.",
        H("ProfiniteQuotientBound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finiteexponentbound"),
                DeclarationHandle.Create(Prefix + "FiniteExponentBound"),
                H("Uniform finite exponent order bound"),
                StatementSource.FromAuthor(Disp(Seq(C("FiniteExponentBound", V("d"), V("m"), V("B")), Sp, Iff, Sp, All("Q", V("Type"), Implies(And(C("Group", V("Q")), C("Finite", V("Q"))), Implies(And(C("GeneratedByAtMost", V("Q"), V("d")), All("q", V("Q"), Eqn(Pow(V("q"), V("m")), D(1)))), Le(C("Card", V("Q")), V("B")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed d, m and B, every finite group with at most d algebraic generators and every element having mth power one has order at most B. This proposition is an explicit unproved finite-group input, of the restricted Burnside form."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closed-normal-finite-quotient-of-bound"),
                DeclarationHandle.Create(Prefix + "closed_normal_finite_quotient_of_bound"),
                H("A closed normal quotient is finite"),
                StatementSource.FromAuthor(Disp(Implies(Profinite(), All("P", C("ClosedNormalSubgroup", G()), All("B", N(), Implies(All("N", C("OpenNormalSubgroup", G()), Implies(Le(V("P"), V("N")), Le(C("Index", V("N")), V("B")))), C("Finite", C("Quotient", G(), V("P"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let P be any closed normal subgroup of a compact totally disconnected topological group. If the indices of all open normal subgroups containing P are at most B, then G modulo P is finite. A maximal index forces a least open normal subgroup; closed-set separation identifies it with P. This includes nontrivial P and assumes no dense generators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-power-quotient-of-exponent-bound"),
                DeclarationHandle.Create(Prefix + "finite_power_quotient_of_exponent_bound"),
                H("Exponent bounds transfer through a closed power subgroup"),
                StatementSource.FromAuthor(Disp(Implies(Profinite(), Implies(Dense(), Implies(And(C("IsClosed", P()), C("FiniteExponentBound", C("Card", V("S")), V("m"), V("B"))), C("Finite", C("Quotient", G(), P()))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For dense finite generators S and a closed power subgroup, the uniform finite exponent order bound applies to every continuous finite quotient killing that subgroup. The general closed normal quotient theorem then makes the power quotient finite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isopen-powersubgroup-of-finite-inputs"),
                DeclarationHandle.Create(Prefix + "isOpen_powerSubgroup_of_finite_inputs"),
                H("Openness from the two finite-group inputs"),
                StatementSource.FromAuthor(Disp(Implies(Profinite(), Implies(Dense(), Implies(Inputs(V("m")), C("IsOpen", P())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a compact totally disconnected topological group with dense generators S, a finite power-width bound and a finite exponent order bound at the same m imply openness of the power subgroup. Both finite-group inputs remain assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiteindex-isopen-of-finite-inputs"),
                DeclarationHandle.Create(Prefix + "finiteIndex_isOpen_of_finite_inputs"),
                H("Arbitrary finite-index subgroups"),
                StatementSource.FromAuthor(Disp(Implies(Profinite(), Implies(Dense(), All("H", C("Subgroup", G()), Implies(C("FiniteIndex", V("H")), Implies(Inputs(C("Index", Core())), C("IsOpen", V("H"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite-index subgroup H, the two finite-group inputs at its positive normal-core index make the contained power subgroup open. Therefore H is open. H is not assumed normal."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula G() => V("G");
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula P() => C("powerSubgroup", G(), V("m"));
    private static Formula Core() => C("NormalCore", V("H"));
    private static Formula Dense() => Eqn(C("TopologicalClosure", C("SubgroupClosure", V("S"))), C("TopSubgroup", G()));
    private static Formula Profinite() => C("CompactTotallyDisconnectedTopologicalGroup", G());
    private static Formula Inputs(Formula m) => And(
        C("FinitePowerWidth", C("Card", V("S")), m, V("w")),
        C("FiniteExponentBound", C("Card", V("S")), m, V("B")));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, Open, V(n), Colon, Sp, t, Close, Comma, Sp, b);
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
