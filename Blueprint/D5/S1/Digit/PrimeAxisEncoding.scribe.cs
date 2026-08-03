using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisEncoding",
            "Prime-indexed canonical W rows encode positive naturals and transport multiplication to table addition."),
        H("Prime-Axis Encoding"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-axis-table-equivalence-and-multiplication"),
                H("Prime-axis table equivalence and multiplication"),
                LeanTheorem(
                    "D5/S1/Digit/PrimeAxisEncoding.prime_axis_encoding_spec"),
                LatexStatement.Create(@"$$\forall z,w \in \operatorname{PrimeAxisTable},\ \operatorname{Bijective}(\operatorname{primeAxisEncoding}) \land \operatorname{coe}_{\mathbb{N}}(\operatorname{primeAxisEncoding}(z)) = \operatorname{decodePrimeAxisTable}(z) \land \operatorname{decodePrimeAxisTable}(\operatorname{normalizedTableAdd}(z,w)) = \operatorname{decodePrimeAxisTable}(z)\operatorname{decodePrimeAxisTable}(w)$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Finitely supported prime axes carrying canonical W rows are equivalent to positive naturals through their factorization exponents. Addition transported through this equivalence decodes exactly as multiplication.")))
            ))));
}
