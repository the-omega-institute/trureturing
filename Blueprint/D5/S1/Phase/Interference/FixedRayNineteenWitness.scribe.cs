using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class FixedRayNineteenWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two admissible cases on the same modulus nineteen have different Jacobi selector values.",
        H("Fixed Ray Nineteen Witness"),
        Blocks(
            Describe.Lean(DescribeId.Create("fixed-ray-modulus"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayModulus"),
                H("The fixed ray modulus is nineteen"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("fixedRayModulus"), Eq, D(1, 9)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The witness fixes the ray datum to the explicit modulus nineteen."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-ray-admissible"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRayAdmissible"),
                H("Admissibility is the inverse-residue congruence"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("fixedRayAdmissible"), Open, F.Id("beta"), Comma, Sp, F.Id("gamma"), Close,
                    Eq, D(4), F.Id("beta"), F.Id("gamma"), Sp, Equiv, Sp, Minus, D(1), Sp,
                    Open, Operatorname, Grp(F.Id("mod")), Sp, D(1, 9), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Admissibility is the frozen inverse-residue condition specialized to modulus nineteen."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-ray-selector"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixedRaySelector"),
                H("The selector is the Jacobi value at nineteen"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("fixedRaySelector"), Open, F.Id("beta"), Close, Eq,
                    Operatorname, Grp(F.Id("jacobi")), Open, F.Id("beta"), Comma, D(1, 9), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selector is defined independently as the Jacobi symbol of the beta numerator at the fixed ray."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-ray-case-one"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_one"),
                H("The first admissible case has selector one"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("fixedRayAdmissible"), Open, D(1), Comma, D(1, 4), Close, Sp, Land, Sp,
                    F.Id("fixedRaySelector"), Open, D(1), Close, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit pair beta one and gamma fourteen satisfies the congruence and has selector one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-ray-case-two"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_case_two"),
                H("The second admissible case has selector minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("fixedRayAdmissible"), Open, D(2), Comma, D(7), Close, Sp, Land, Sp,
                    F.Id("fixedRaySelector"), Open, D(2), Close, Eq, Minus, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The explicit pair beta two and gamma seven satisfies the same congruence at nineteen and has selector minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-ray-nineteen-witness"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.fixed_ray_nineteen_witness"),
                H("The same ray admits unequal selectors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("beta"), Comma, F.Id("gamma"), Comma, F.Id("betaPrime"), Comma,
                    F.Id("gammaPrime"), InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("fixedRayAdmissible"), Open, F.Id("beta"), Comma, F.Id("gamma"), Close,
                    Sp, Land, Sp, F.Id("fixedRayAdmissible"), Open, F.Id("betaPrime"), Comma,
                    F.Id("gammaPrime"), Close, Sp, Land, Sp,
                    F.Id("fixedRaySelector"), Open, F.Id("beta"), Close, Neq, Sp,
                    F.Id("fixedRaySelector"), Open, F.Id("betaPrime"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two displayed cases share the same modulus nineteen but their selector values differ, providing the concrete fixed-ray refutation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-fixed-ray-character"),
                DeclarationHandle.Create("D5/S1/Phase/Interference/FixedRayNineteenWitness.no_fixed_ray_character"),
                H("No ray-only character fits both cases"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, Exists, Sp, F.Id("chi"), Colon, Sp, Mathbb, Grp(F.Id("Z")), To, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Forall, Sp, F.Id("beta"), Comma, F.Id("gamma"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("fixedRayAdmissible"), Open, F.Id("beta"), Comma, F.Id("gamma"), Close, Sp, Rightarrow, Sp,
                    F.Id("fixedRaySelector"), Open, F.Id("beta"), Close, Eq, F.Id("chi"), Open,
                    F.Id("fixedRayModulus"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any function of the fixed ray value would assign the same result to both admissible cases, contradicting their checked unequal selectors."))),
                DescribeRole.Theorem))));
}
