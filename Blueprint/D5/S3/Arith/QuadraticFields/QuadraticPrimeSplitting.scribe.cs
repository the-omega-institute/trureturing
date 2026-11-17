using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.QuadraticFields;

internal sealed class QuadraticPrimeSplittingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimal polynomial modulo every rational prime gives the actual maximal-order Euler polynomial through index-one Kummer-Dedekind. Quadratic reciprocity identifies the odd-prime factors. At two the polynomial is treated separately in the two mod8 cases; at p it is ramified. No prime is omitted.", H("QuadraticPrimeSplitting"), Blocks(
            Paragraph(Text("The minimal polynomial modulo every rational prime gives the actual maximal-order Euler polynomial through index-one Kummer-Dedekind. Quadratic reciprocity identifies the odd-prime factors. At two the polynomial is treated separately in the two mod8 cases; at p it is ramified. No prime is omitted.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-quadraticrootequivsqrts"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadraticRootEquivSqrts"), H("quadraticRootEquivSqrts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Completing the square is a genuine bijection of root types in every odd field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-quadratic-root-card"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_root_card"), H("quadratic_root_card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Root count for the half-integral quadratic generator, including the ramified case."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-quadratic-euler-polynomial-general"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_euler_polynomial_general"), H("General quadratic Euler polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The general polynomial X²-bX-a has local Euler polynomial determined by its discriminant b²+4a, including repeated ramified factors. The half-integral signature is retained as its b=1 application; the imaginary Merca field uses b=0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-quadratic-euler-polynomial"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.quadratic_euler_polynomial"), H("quadratic_euler_polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The product over distinct irreducible factors is the local Euler polynomial. Repeated factors contribute only once, so this also handles ramified primes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-negative-prime-reciprocity"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.negative_prime_reciprocity"), H("negative_prime_reciprocity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The discriminant character is the conductor-p quadratic character, including at p. The prime two is treated separately because the integral generator has denominator two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-integralgenerator-root-card"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_root_card"), H("integralGenerator_root_card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The roots of the actual integral generator polynomial at each odd rational prime. This identifies its linear factors using the same character as the original double sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-integralgenerator-euler-polynomial"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial"), H("integralGenerator_euler_polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The local factor supplied to Kummer-Dedekind is expressed by the original conductor-p character, at every odd prime including the ramified prime p."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-integralgenerator-euler-polynomial-two"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_two"), H("integralGenerator_euler_polynomial_two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At two the half-integral polynomial is irreducible for p congruent to three mod eight and has two distinct linear factors for p congruent to seven mod eight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-integralgenerator-euler-polynomial-all"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.integralGenerator_euler_polynomial_all"), H("integralGenerator_euler_polynomial_all"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every rational prime, including two and the ramified prime p."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticprimesplitting-primeideal-euler-polynomial"),
                DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticPrimeSplitting.primeIdeal_euler_polynomial"), H("primeIdeal_euler_polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Actual prime ideals over every rational prime have the quadratic Euler factor. The maximal-order generator theorem discharges the index condition at every prime."))), DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator"))]));
}
