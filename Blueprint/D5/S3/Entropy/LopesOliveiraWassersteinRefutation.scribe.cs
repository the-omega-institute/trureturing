using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class LopesOliveiraWassersteinRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/lopesoliveira2026transport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LopesOliveiraWassersteinRefutation", H("Lopes Oliveira Wasserstein Refutation"), Blocks(
            Paragraph(Text("The registered claim is the preregistered fixed-classical-target extension of the authors' section 8 similar-expression question. It ranges over every integer d at least 2, every real Holder potential on the original positive-index full shift, and every Borel probability law, with one finite real c depending on d and the potential. It explicitly requires the unique invariant classical KS variational equilibrium for that same potential. KS entropy is the supremum over all finite measurable partitions of the limiting normalized entropy of their iterated joins. The binary constant potential minus log 2 has the proved actual unique fair Bernoulli equilibrium. Its pressure-maximizing noninvariant comparison law has zero deficit and transport distance at least 1/8, so no real c satisfies the displayed inequality. The contradiction includes negative and zero c. There is no restriction to invariant, absolutely continuous, full-support or Markov comparison laws and no extra logarithmic-integrability hypothesis. This settles that fixed extension only; it does not claim to settle every interpretation of the authors' broader open question, and it uses neither a replacement equilibrium nor a finite-tail surrogate.")),
            Describe.Lean(DescribeId.Create("isclassicalequilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsClassicalEquilibrium"),
                H("IsClassicalEquilibrium"), StatementSource.FromAuthor(ClassicalFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isuniqueclassicalequilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.IsUniqueClassicalEquilibrium"),
                H("IsUniqueClassicalEquilibrium"), StatementSource.FromAuthor(UniqueFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.claim"),
                H("claim"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("binary-classical-equilibrium"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.binary_classical_equilibrium"),
                H("binary classical equilibrium"), StatementSource.FromAuthor(BinaryFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result"),
                H("result"), StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The definitions and conventions in the introduction apply. The result refutes the registered fixed-classical-target extension; the authors' broader similar-expression question remains outside this settlement."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lopes-oliveira-2026-fixed-classical-target-wasserstein"),
                    ResolutionKind.Refuted)))));
    private static Formula V(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. xs]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
    private static Formula Logic(Formula l, FormulaLogicOperator op, Formula r) => new Formula.Logic(l, op, r);
    private static Formula AndF(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula EqualF(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula RealType => Seq(Mathbb, Grp(V("R")));
    private static Formula NatType => Seq(Mathbb, Grp(V("N")));
    private static Formula Space(Formula d) => C("Omega", d);
    private static Formula LawType(Formula d) => C("Measure", Space(d));
    private static Formula PotentialType(Formula d) => new Formula.TypeArrow(Space(d), RealType);
    private static Formula PotentialIntegral(Formula d, Formula phi, Formula nu) => Seq(
        new Formula.Subscript(Int, Seq(V("x"), Colon, Space(d))),
        new Formula.Apply(phi, [V("x")]), Sp, Mathrm, Grp(V("d")), nu);
    private static Formula Objective(Formula d, Formula phi, Formula nu, Formula hT) => Seq(
        PotentialIntegral(d, phi, nu), Plus, C("ksEntropy", hT));
    private static Formula Preserves(Formula nu) => C("MeasurePreserving", V("shift"), nu, nu);
    private static Formula ClassicalFormula()
    {
        var d = V("d"); var phi = V("phi"); var mu = V("mu"); var rho = V("rho");
        return Disp(All("d", NatType, All("phi", PotentialType(d), All("mu", LawType(d),
            Logic(C("IsClassicalEquilibrium", phi, mu), FormulaLogicOperator.Iff,
                AndF(C("IsProbabilityMeasure", mu), Ex("hT", Preserves(mu),
                    All("rho", LawType(d), Imp(C("IsProbabilityMeasure", rho),
                        All("hR", Preserves(rho), Rel(Objective(d, phi, rho, V("hR")),
                            FormulaRelationOperator.LessThanOrEqual, Objective(d, phi, mu, V("hT")))))))))))));
    }
    private static Formula UniqueFormula()
    {
        var d = V("d"); var phi = V("phi"); var mu = V("mu"); var rho = V("rho");
        return Disp(All("d", NatType, All("phi", PotentialType(d), All("mu", LawType(d),
            Logic(C("IsUniqueClassicalEquilibrium", phi, mu), FormulaLogicOperator.Iff,
                AndF(C("IsClassicalEquilibrium", phi, mu), All("rho", LawType(d),
                    Imp(C("IsClassicalEquilibrium", phi, rho), EqualF(rho, mu)))))))));
    }
    private static Formula ClaimFormula()
    {
        var d = V("d"); var dn = C("toNat", d); var phi = V("phi"); var mu = V("mu"); var nu = V("nu");
        var deficit = Seq(C("niPressure", phi), Minus, C("niEntropy", nu), Minus, PotentialIntegral(dn, phi, nu));
        var bound = Rel(C("wassersteinOne", nu, mu), FormulaRelationOperator.LessThanOrEqual,
            Seq(V("c"), Cdot, Sqrt, Grp(deficit)));
        return Disp(Logic(V("claim"), FormulaLogicOperator.Iff,
            All("d", Seq(Mathbb, Grp(V("Z"))), Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, d),
                All("phi", PotentialType(dn), Imp(C("IsHolder", phi),
                    Ex("mu", LawType(dn), AndF(C("IsUniqueClassicalEquilibrium", phi, mu),
                        Ex("c", RealType, All("nu", LawType(dn), Imp(C("IsProbabilityMeasure", nu), bound)))))))))));
    }
    private static Formula BinaryFormula() => Disp(C("IsUniqueClassicalEquilibrium",
        Seq(V("Function"), Dot, V("const"), Open, Space(D(2)), Comma, Minus, Log, D(2), Close),
        Seq(V("SourceEquilibrium"), Dot, V("fair"))));
}
