using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Generic;

internal sealed class CertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An executable full certificate at arbitrary accuracy.",
        H("An executable full certificate at arbitrary accuracy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("generic-certificate-full-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate"),
                H("All rational polynomials and signed shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive natural radius R, rational shift s and positive rational requested width eta, every pair of finite rational coefficient lists produces a successful full Boolean certificate. The produced rational bounds enclose the genuine full Lebesgue translation energy of literalRationalTest and have width strictly less than eta.")),
                    Paragraph(Text("The theorem also quantifies over every pair of rational polynomials p and q: finite lists representing them exist, and the same executable list producer satisfies the complete certificate statement for p and q. The polynomial representation theorem is used only in the proof; it is not an opaque decision in the list algorithm.")),
                    Paragraph(Text("The executable depth rule is Nat.log 2 (Nat.ceil (2C/eta))+1. The requested binary precision is computed from eta. Separate logarithmic depth budgets bound the mesh contribution Cl L^2/2^d and scalar contribution Ce L/2^m by strict half-widths. Structural all-cell acceptance, exact index alignment and the hull mass bounds prove full checker success without assuming it."))),
                DescribeRole.Theorem)),
        []));
}
