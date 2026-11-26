using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class BojicRule150Document : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/bojic2026semisimple");

    private static Formula LocalLcm()
    {
        Formula k = F.Id("k"), m = F.Id("m"), q = F.Id("q"), f = F.Id("f");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula factors = Seq(F.Id("S"), Underscore, Grp(q));
        Formula semisimple = Seq(F.Id("u"), Underscore, Grp(k, Comma, m, Comma, f));
        Formula lcm = Seq(Operatorname, Grp(F.Id("lcm")), Underscore,
            Grp(f, Sp, InMacro, Sp, factors), Sp,
            Operatorname, Grp(F.Id("ord")), Open, semisimple, Close);
        return Disp(Seq(
            Forall, Sp, k, Comma, m, Sp, InMacro, Sp, naturals, Comma, Sp,
            Neg, Open, D(3), Sp, Mid, Sp, q, Close,
            Sp, Implies, Sp, lcm, Sp, Eq, Sp, q));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For cyclic Rule 150 with admissible Mersenne odd part q, the LCM of the local "
        + "semisimple orders on the nontrivial primary factors is q.",
        H("The local semisimple-order LCM for Rule 150"),
        Blocks(Describe.Lean(
            DescribeId.Create("bojic-rule-150-local-lcm"),
            DeclarationHandle.Create(Result),
            H("The LCM is the Mersenne odd part"),
            StatementSource.FromAuthor(LocalLcm()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For natural numbers k and m, set q = 2^k − 1 and assume that 3 does "
                    + "not divide q. This forces k to be positive, since 3 divides 0. "
                    + "Put n = 2^m q. For each distinct "
                    + "monic irreducible factor f of X^q − 1 over F₂ besides X + 1, take "
                    + "the class of G = 1 + X + X^(n − 1) in F₂[X]/(f^(2^m)). "
                    + "The formula uses S_q for this set of factors and u_(k,m,f) for the "
                    + "odd-order semisimple part of the class indexed by f. At k = 1, "
                    + "q = 1 and the index set is empty. Its LCM is 1.")),
                Paragraph(Text(
                    "Section 2.3 leaves this identity open. Theorem 8.8 describes the "
                    + "semisimple part, and Theorem 8.19 uses the local odd orders in the "
                    + "global period formula for q > 1. The formal construction takes "
                    + "the power G^((2^k)^m) in each primary quotient. It is the unique "
                    + "odd-order unit whose product with a cofactor 1 + ν gives the local "
                    + "multiplier, where ν is nilpotent and reduces to zero modulo f. "
                    + "Its order equals the order of G modulo f.")),
                Paragraph(Text(
                    "Frobenius gives q as a common exponent in the residue fields. "
                    + "If d is the LCM of the residue orders, then X^q − 1 divides "
                    + "(1 + X + X²)^d − X^d. The nonzero polynomial on the right has "
                    + "degree at most 2d. Thus q ≤ 2d, and q/d is an odd integer, "
                    + "so d = q."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bojic-2026-rule-150-local-lcm"),
                ResolutionKind.Proved)))));
}
