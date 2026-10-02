using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Dedekind;

internal sealed class TameDifferentDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/tauceti2026tamedifferent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-power quotient filtration computes the residue trace, and a Chinese "
            + "remainder lift detects the tame different exponent.",
        H("Prime-Power Traces and Dedekind's Different"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-quotient-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Dedekind/TameDifferent.prime_power_quotient_trace"),
                H("Trace on a prime-power quotient"),
                StatementSource.FromAuthor(TraceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let A and B be commutative rings, with B a module-finite A-algebra "
                            + "and a Dedekind domain. Let p and P be maximal ideals in A and B, "
                            + "with P nonzero. For any natural n, assume both B/P to the n and "
                            + "B/P carry A/p-algebra structures compatible with the A actions. "
                            + "For every z in B, the trace of its image in B/P to the n "
                            + "is n times its trace in B/P. The zero exponent is included.")),
                    Paragraph(Text(
                        "Multiplication by an element in P to the n but outside P to the "
                            + "n plus one gives the first map in an exact quotient sequence. "
                            + "After splitting that sequence over the residue field, the "
                            + "multiplication operator has two diagonal blocks and a zero-trace "
                            + "off-diagonal block. Induction gives the formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-power-divides-different"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Dedekind/TameDifferent.prime_power_divides_different_iff"),
                H("The next prime power detects wild ramification"),
                StatementSource.FromAuthor(DifferentFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let A and B be Dedekind domains with B finite and torsion free "
                            + "over A, and with separable fraction-field extension. Let p "
                            + "be a nonzero maximal ideal of A and P a maximal ideal of B "
                            + "over p. If pB equals P to the e times a coprime ideal Q, "
                            + "then P to the e divides the different exactly when the "
                            + "residue extension is inseparable or e vanishes in A/p.")),
                    Paragraph(Text(
                        "The inverse fractional ideal converts different divisibility into "
                            + "integral trace membership. The Chinese remainder decomposition "
                            + "turns this trace into e times the residue trace. In the tame "
                            + "case a residue with nonzero trace lifts into Q and excludes "
                            + "divisibility by P to the e.")),
                    Paragraph(Text(
                        "Together with the pinned universal lower bound, the criterion "
                            + "computes the different exponent as e minus one at tame primes. "
                            + "Golden cubic field discriminants also require their actual "
                            + "prime support, ramification indices, completion maps and the "
                            + "global different-to-discriminant calculation."))),
                DescribeRole.Theorem))));

    private static Formula TraceFormula()
    {
        Formula n = F.Id("n");
        Formula z = F.Id("z");
        return Disp(Seq(Forall, Sp, n, Comma, Sp, z, Comma, Sp,
            Call("quotientPowerTrace", n, z), Sp, Eq, Sp, n, Sp,
            Call("residueTrace", z)));
    }

    private static Formula DifferentFormula()
    {
        Formula e = F.Id("e");
        Formula p = F.Id("P");
        return Disp(Seq(new Formula.Power(p, e), Sp, F.Id("divides"), Sp,
            Call("different", F.Id("B"), F.Id("A")), Sp, Iff, Sp,
            Call("ResidueInseparable", p), Sp, Lor, Sp,
            Call("residueCast", e), Sp, Eq, Sp, D(0)));
    }
}
