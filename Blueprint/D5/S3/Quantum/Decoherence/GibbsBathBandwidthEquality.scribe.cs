using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class GibbsBathBandwidthEqualityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.";

    private static readonly LibraryNoteRef Cooling =
        LibraryNoteRef.Create("D5/L/Entropy/allahverdyan2011thermodynamic");
    private static readonly LibraryNoteRef FiniteBath =
        LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bath sizes, output rigidity and heat at minimum Gibbs bandwidth for a two-eigenvalue record.",
        H("Equality at minimum Gibbs bath bandwidth"),
        Blocks(
            Paragraph(
                Text("Consider d equally likely labels with linearly independent normalized pure records. Their average record state has d-dimensional support in the original record space. Write ρ for the state on that support and let its two distinct eigenvalues μ₊ > μ₋ > 0 have multiplicities p and q, with p + q = d.")),
            Paragraph(
                Text("One unrestricted unitary acts on the label, the bath and the original record space. The bath starts independently in a finite Gibbs state at inverse temperature β > 0. The output must have a prescribed pure label and the original average record marginal. The support reduction in "),
                Ref("D5/S3/Quantum/Decoherence/LabelResetBandwidth"),
                Text(" connects this reset to the Gibbs preparation bound in "),
                Ref("D5/S3/Quantum/Decoherence/GibbsBathBandwidth"),
                Text(". The least bandwidth over finite baths is W = β⁻¹ log(μ₊/μ₋).")),
            Describe.Lean(
                DescribeId.Create("minimum-width-ambient-product"),
                DeclarationHandle.Create(Module + "minimumWidth_ambient_product"),
                H("The ambient output is a product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(FiniteBath),
                Blocks(
                    Paragraph(Text("At bandwidth W every admissible unitary gives the prescribed pure label tensored with the maximally mixed bath I_b/b and the original average record. The ambient formula embeds ρ into its original support and retains the ambient zero modes.")),
                    Paragraph(Text("The ratio equality saturates both marginal endpoint bounds. The positive slacks in the joint endpoint bounds annihilate the bath tensor each corresponding record eigenspace. The two record eigenspaces exhaust the support, forcing the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-width-bath-multiplicities"),
                DeclarationHandle.Create(Module + "minimumWidth_bath_multiplicities"),
                H("The bath has two energies with fixed multiplicities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Cooling),
                Blocks(
                    Paragraph(Text("In the reduced preparation orbit the bath has only its lowest and highest energies, of multiplicities bp/d and bq/d, respectively, where b is the bath dimension. Equality of the input and output spectra forces both counts. The corresponding Gibbs eigenweights are dμ₊/b and dμ₋/b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-width-ambient-dimension"),
                DeclarationHandle.Create(Module + "minimumWidth_ambient_dimension_iff"),
                H("Exact bath dimensions at minimum bandwidth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Cooling, FiniteBath),
                Blocks(
                    Paragraph(Text("The smallest bath dimension at W is d/gcd(d,p). The admissible dimensions are exactly b = k·d/gcd(d,p) for integers k ≥ 1. Each such dimension admits a bath with energies 0 and W and the required multiplicities. The input and product output have matching spectra on the support, which gives a unitary and lifts to a single unitary on the original ambient space.")),
                    Paragraph(Text("Allahverdyan et al., arXiv:1107.1044v1, §IV.B, Eqs. (31)–(32), give the even-bath binary cooling threshold and equal endpoint multiplicities. At zero target gap their population formula inverts to the d = 2 bandwidth threshold. Reeb and Wolf, arXiv:1306.4352v3, §3.3, Eqs. (29)–(32) and the construction on p. 12, give the finite-reservoir lower spectral bound and the engineered Gibbs swap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-width-ambient-heat"),
                DeclarationHandle.Create(Module + "minimumWidth_ambient_heat"),
                H("The actual ambient bath heat at the optimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(FiniteBath),
                Blocks(
                    Paragraph(Text("The heat is the bath energy increase, computed from the bath marginal of the actual ambient output. Every admissible dimension at W gives ΔQ = Wq(1/d − μ₋) = Wpq(μ₊ − μ₋)/d, including the smallest bath.")),
                    Paragraph(Text("The high-energy weight increases from qμ₋ to q/d. The weights on the two energy spaces sum to one before and after the operation, so a common shift of the energies cancels."))),
                DescribeRole.Theorem))));
}
