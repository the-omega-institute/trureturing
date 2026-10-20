using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class FiniteRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite cyclic action realizes a divisor table exactly when its Mobius data count whole cycles.",
        H("Finite Realization of Periodic-Point Tables"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-realization-iff"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/FiniteRealization.finite_realization_iff"),
                H("The finite divisor-table criterion"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(
                    Paragraph(Text("Fix a positive natural M and a natural-valued table a. "
                        + "There is a permutation of Fin (a M), with Mth power the identity "
                        + "and fixed count a d for every divisor d of M, exactly when the "
                        + "integer Mobius transform at each such d is nonnegative and "
                        + "divisible by d. In the formula A(sigma,d) is the actual fixedCount, "
                        + "and delta is the integer factor-pair Mobius transform defined in OrbitCounting.")),
                    Paragraph(Text("The converse takes delta(a,d) divided by d copies of "
                        + "the cyclic set ZMod d and advances every copy by one. Mobius "
                        + "inversion gives the required fixed counts. At time M every "
                        + "point returns, so the total carrier has cardinality a M and "
                        + "can be relabeled by Fin (a M). This is a finite restriction of "
                        + "the classical exact-realization criterion.")),
                    Paragraph(Text("The table's value at zero and its values away from "
                        + "divisors of M are unused. The empty carrier, M equal to one, "
                        + "and singleton cycles are included. The permutation's order "
                        + "divides M; equality of the order with M and transitivity are "
                        + "not asserted. Positive-time fixed counts extend along the "
                        + "greatest common divisor with M, so arbitrary prescribed "
                        + "outside-divisor values cannot be inferred."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        Formula a = F.Id("a"), m = F.Id("M"), d = F.Id("d"), sigma = SigmaLower;
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula transform = Seq(Delta, Open, a, Comma, d, Close);
        Formula table = Seq(Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            d, Mid, Sp, m, Rightarrow, Sp, Call("A", sigma, d), Eq, Call("a", d));
        Formula arithmetic = Seq(Forall, Sp, d, InMacro, Sp, naturals, Comma, Sp,
            d, Mid, Sp, m, Rightarrow, Sp, D(0), Leq, Sp, transform, Land, Sp, d, Mid, Sp, transform);
        return Disp(Seq(Forall, Sp, a, Colon, naturals, To, Sp, naturals, Comma, Sp,
            m, InMacro, Sp, naturals, Underscore, Grp(Gt, D(0)), Comma, Sp,
            Open, Exists, Sp, sigma, Colon, Call("Perm", Call("Fin", Call("a", m))),
            Comma, Sp, sigma, Caret, Grp(m), Eq, D(1), Land, Sp, Open, table, Close,
            Close, Iff, Sp, Open, arithmetic, Close));
    }

}
