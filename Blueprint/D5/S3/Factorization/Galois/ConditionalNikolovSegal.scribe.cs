using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ConditionalNikolovSegalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/ConditionalNikolovSegal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong completeness conditional on two explicit finite-group propositions.",
        H("ConditionalNikolovSegal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-nikolov-segal"),
                DeclarationHandle.Create(Prefix + "conditional_nikolov_segal"),
                H("Conditional strong completeness"),
                StatementSource.FromAuthor(Disp(Implies(All("d", N(), All("m", N(), Implies(Seq(D(0), Sp, Lt, Sp, V("m")), Ex("w", N(), C("FinitePowerWidth", V("d"), V("m"), V("w")))))), Implies(All("d", N(), All("m", N(), Implies(Seq(D(0), Sp, Lt, Sp, V("m")), Ex("B", N(), C("FiniteExponentBound", V("d"), V("m"), V("B")))))), All("G", V("Type"), Implies(Profinite(), Implies(Ex("S", C("Finset", G()), Dense()), All("H", C("Subgroup", G()), Implies(C("FiniteIndex", V("H")), C("IsOpen", V("H"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume, for every d and positive m, an ordered mth-power width bound for every finite d-generated group, and a finite order bound for every such group of exponent dividing m. Then every finite-index subgroup of an arbitrary compact totally disconnected topological group generated densely by some finite set is open. Both deep finite-group propositions are premises. This is the full strong-completeness conclusion conditional on those premises; neither deep theorem is proved here. The power-width input is the Nikolov and Segal result Powers in finite groups (2011), DOI 10.4171/GGD/136. The order-bound input is the restricted Burnside theorem of Zelmanov. The unconditional strong-completeness theorem is Nikolov and Segal (2007), DOI 10.4007/annals.2007.165.171."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula G() => V("G");
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Dense() => Eqn(C("TopologicalClosure", C("SubgroupClosure", V("S"))), C("TopSubgroup", G()));
    private static Formula Profinite() => C("CompactTotallyDisconnectedTopologicalGroup", G());
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
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
