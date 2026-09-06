using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class GautschiEvenInterpolationBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/GautschiEvenInterpolationBounds.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gautschi-type finite products bound the actual Mathlib Lagrange basis on squared nodes, keeping direct and reflected separation explicit.",
        H("Conditioning of Even Lagrange Interpolation"),
        Blocks(
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-squaredNodeBudget"),
                DeclarationHandle.Create(Prefix + "squaredNodeBudget"), H("Finite conditioning product"),
                StatementSource.FromAuthor(Disp(F.Id("G_i(R)=product over j!=i of (R^2+A_j^2)/d_ij."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The radius and gap data can be rational. Positive gap hypotheses appear on every soundness theorem; totalized division at zero supplies no certificate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-lagrange-squared-basis-norm-le"),
                DeclarationHandle.Create(Prefix + "lagrange_squared_basis_norm_le"), H("Actual Lagrange basis on a disk"),
                StatementSource.FromAuthor(Disp(F.Id("For |w|<=R, |z_j|<=A_j and 0<d_ij<=|z_i^2-z_j^2|, |L_i(w^2)|<=G_i(R)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand Mathlib Lagrange.basis into basisDivisor factors. Apply the triangle inequality to each numerator and the certified lower bound to each denominator. This is the product mechanism in Gautschi (1962), Sections 2-3, specialized to squared nodes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-squaredNodeBudget-le-growth"),
                DeclarationHandle.Create(Prefix + "squaredNodeBudget_le_growth"), H("Explicit polynomial growth"),
                StatementSource.FromAuthor(Disp(F.Id("For R>=1 and positive gaps, G_i(R)<=R^(2*card(s.erase i))*G_i(1)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each numerator R^2+A_j^2 is at most R^2*(1+A_j^2). Multiply the finite nonnegative inequalities. No inverse-matrix condition number is left unspecified."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-lagrange-squared-interpolate-norm-le"),
                DeclarationHandle.Create(Prefix + "lagrange_squared_interpolate_norm_le"), H("Seed-normalized interpolation bound"),
                StatementSource.FromAuthor(Disp(F.Id("With the same radii and gaps, and |seed_i|>=mu>0, |interpolate(s,z^2,values/seed)(w^2)|<=sum_i (|values_i|/mu)*G_i(R)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the actual existing interpolate linear map and the basis estimate. The source integrates classical interpolation estimates; it makes no independent novelty claim for Gautschi bounds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-squared-gap-factorization"),
                DeclarationHandle.Create(Prefix + "squared_gap_factorization"), H("Both types of collision matter"),
                StatementSource.FromAuthor(Disp(F.Id("|z^2-w^2|=|z-w|*|z+w|."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial difference-of-squares factorization and multiplicativity of the complex norm give the equality. Separating only direct neighbors cannot certify even interpolation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gautschieveninterpolationbounds-squared-gap-lower-bound"),
                DeclarationHandle.Create(Prefix + "squared_gap_lower_bound"), H("Transport certified node separations"),
                StatementSource.FromAuthor(Disp(F.Id("Nonnegative d<=|z-w| and e<=|z+w| imply d*e<=|z^2-w^2|."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the arithmetic interface for rigorous node enclosures. The lower bounds must be certified against the actual complex nodes."))), DescribeRole.Theorem)), []));
}
