using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FixedAlgebra;

internal sealed class PrimeDephasingRefinementAbsorptionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite profile observations form an absorbing family of record-channel dephasings.",
        H("Prime-Dephasing Refinement Absorption"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("restricted-prime-profile"),
                DeclarationHandle.Create(Prefix + "restrictedPrimeProfile"),
                H("Restricted prime profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Restrict each finite system address's supplied valuation profile to the "
                        + "observed finite index set S."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profile-class-representative"),
                DeclarationHandle.Create(Prefix + "profileClassRepresentative"),
                H("Profile-class representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose the least finite address in the same restricted-profile fiber. "
                        + "This finite representative avoids any finiteness assumption on the "
                        + "valuation's codomain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orthogonal-profile-record"),
                DeclarationHandle.Create(Prefix + "orthogonalProfileRecord"),
                H("Orthogonal profile record"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Encode every profile fiber by the standard basis vector at its canonical "
                        + "representative, so equal fibers have Gram overlap one and distinct "
                        + "fibers have overlap zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-dephasing-channel"),
                DeclarationHandle.Create(Prefix + "primeDephasing"),
                H("Finite-prime dephasing channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the repository's canonical recordChannel to the orthogonal record "
                        + "of the S-restricted valuation profile. No second channel formula is "
                        + "introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-dephasing-refinement-absorption"),
                DeclarationHandle.Create(
                    Prefix + "prime_dephasing_refinement_absorption"),
                H("Refinement absorption"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If S is contained in T, equality of T-profiles implies equality of "
                            + "S-profiles. Entrywise, the finer zero-one Gram mask therefore "
                            + "absorbs the coarser mask in either order.")),
                    Paragraph(Text(
                        "The statement records all three requested equalities: commutation, "
                            + "finer-after-coarser absorption, and coarser-after-finer "
                            + "absorption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-dephasing-idempotent"),
                DeclarationHandle.Create(Prefix + "prime_dephasing_idempotent"),
                H("Idempotence at equal index sets"),
                StatementSource.FromAuthor(IdempotenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specializing refinement to S equals T recovers idempotence directly from "
                        + "the absorption theorem."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("prime-dephasing-empty"),
                DeclarationHandle.Create(Prefix + "prime_dephasing_empty"),
                H("Empty observation is the identity"),
                StatementSource.FromAuthor(EmptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All profiles restricted to the empty set are equal, so no matrix entry is "
                        + "discarded."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("prime-dephasing-univ-absorption"),
                DeclarationHandle.Create(Prefix + "prime_dephasing_univ_absorption"),
                H("The full index set absorbs every subset"),
                StatementSource.FromAuthor(UnivFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite index type, every S is contained in the full set. The three "
                        + "refinement equalities therefore hold with T equal to the universe."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("refinement-subset-is-necessary"),
                DeclarationHandle.Create(Prefix + "refinement_subset_is_necessary"),
                H("The refinement premise is necessary"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On two addresses, a singleton observed index distinguishes the addresses "
                        + "while the empty target observation preserves their off-diagonal "
                        + "entry. Thus finer-first absorption fails when S is not contained in "
                        + "T."))),
                DescribeRole.Proposition))));

    private static Formula RefinementFormula()
    {
        Formula source = F.Id("S");
        Formula target = F.Id("T");
        Formula sourceMap = Dephasing(source);
        Formula targetMap = Dephasing(target);
        return Disp(new Formula.Aligned([
            Seq(source, Sp, Subseteq, Sp, target, Sp, Rightarrow),
            Seq(targetMap, Sp, Circ, Sp, sourceMap, Sp, Eq, Sp,
                sourceMap, Sp, Circ, Sp, targetMap, Sp, Land),
            Seq(targetMap, Sp, Circ, Sp, sourceMap, Sp, Eq, Sp,
                targetMap, Sp, Land),
            Seq(sourceMap, Sp, Circ, Sp, targetMap, Sp, Eq, Sp, targetMap, Dot),
        ]));
    }

    private static Formula IdempotenceFormula()
    {
        Formula map = Dephasing(F.Id("S"));
        return Disp(Seq(map, Sp, Circ, Sp, map, Sp, Eq, Sp, map, Dot));
    }

    private static Formula EmptyFormula() =>
        Disp(Seq(Dephasing(Emptyset), Sp, Eq, Sp, F.Id("id"), Dot));

    private static Formula UnivFormula()
    {
        Formula sourceMap = Dephasing(F.Id("S"));
        Formula fullMap = Dephasing(F.Id("univ"));
        return Disp(new Formula.Aligned([
            Seq(fullMap, Sp, Circ, Sp, sourceMap, Sp, Eq, Sp,
                sourceMap, Sp, Circ, Sp, fullMap, Sp, Land),
            Seq(fullMap, Sp, Circ, Sp, sourceMap, Sp, Eq, Sp,
                fullMap, Sp, Land),
            Seq(sourceMap, Sp, Circ, Sp, fullMap, Sp, Eq, Sp, fullMap, Dot),
        ]));
    }

    private static Formula NecessityFormula()
    {
        Formula source = Seq(OpenBrace, D(1), CloseBrace);
        Formula target = Emptyset;
        Formula sourceMap = Dephasing(source);
        Formula targetMap = Dephasing(target);
        return Disp(Seq(
            Neg, Grp(source, Sp, Subseteq, Sp, target), Sp, Land, Sp,
            targetMap, Sp, Circ, Sp, sourceMap, Sp, Neq, Sp, targetMap, Dot));
    }

    private static Formula Dephasing(Formula indexSet) =>
        new Formula.Subscript(F.Id("E"), indexSet);
}
