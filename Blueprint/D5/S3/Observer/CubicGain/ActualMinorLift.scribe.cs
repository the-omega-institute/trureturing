using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class ActualMinorLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The selected lift from the actual primitive normalized source minors",
        H("ActualMinorLift"),
        Blocks(
        Paragraph(Text("The source is VI, Definition 4.1 and equations (4.2)-(4.4). The twenty-eight rows remain r^13 E0 through E0 followed by r^13 E1 through E1, in twenty-nine columns r^28 through 1. The literal source polynomials are instantiated over the integer polynomial ring in b. Retaining the first twenty-seven columns and then the r or constant column defines the integer determinant polynomials a0 and c0. Evaluation is transported through coefficient extraction, the two fixed column selections, and the determinant ring-homomorphism identity. Thus their evaluations are exactly the original real fixed minors.")),
        Paragraph(Text("Let g be the gcd of a0 and c0 in Q[b]. Clear its denominators, take the integer primitive part, and normalize the leading sign to obtain h. The proof establishes that h is primitive, has positive leading coefficient, and maps to a nonzero rational scalar times g. These properties identify the source operation pp_+(g). Gauss's lemma transports the divisibility of g back to h dividing both integer determinant polynomials. Consequently the exact rational quotients a=a0/h and c=c0/h are maps of integer polynomials.")),
        Paragraph(Text("The same global factorization data also imply that actualReducedA and actualReducedC are coprime in Q[b], without selecting a parameter. Write p=a0 and q=c0 after coefficient extension to Q, and g=gcd(p,q). The primitive h is nonzero, and its rational image is u g for a nonzero rational u, so g is nonzero. Exact factorization gives p/g=u a and q/g=u c. The mathlib theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero makes these two products coprime; coprimality passes to their factors a and c. This applies selected_source_normalized_lift's global normalization conjuncts and does not require the proposed displayed factorization of h or any of the unproved degree claims.")),
        Paragraph(Text("At b=criticalRoot and r=liftedR(b), selected_minor_nonzero supplies the nonzero original leading determinant and selected_root_common_zero supplies r a0(b)+c0(b)=0. Factoring a0=h A and c0=h C shows that both h(b) and A(b) are nonzero. Cancellation of this same evaluated common factor gives r=-C(b)/A(b). The exact quotient maps then identify this ratio with the source-normalized rational polynomials actualReducedA and actualReducedC. The nonzero rational scalar used to represent the gcd does not affect the ratio because the same factor is removed from both determinants.")),
        Paragraph(Text("The ratio identification is local at the actual selected algebraic parameter; the quotient normalization and coprimality above are global. The full determinant factorization, the actual h,a,c degree claims in VI (4.3), the universal complex-root and three-equation assertions, and the broader parents 15.2 and 15.3 remain open. The clock-five/six/seven source equations and the complete-world distinctions retain their original scope.")),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-leading-determinant"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorA0"),
            H("actual leading fixed determinant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The integer polynomial determinant of the literal fixed minor retaining columns r^28 through r. Its entries are the b-polynomial coefficients of the original shifted source equations."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-constant-determinant"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualMinorC0"),
            H("actual constant fixed determinant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The integer polynomial determinant retaining columns r^28 through r^2 and the constant column, in the original order."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-integer-polynomial-evaluation"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.evalB"),
            H("real evaluation of an integer polynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each real b, evalB(b) is the ring homomorphism from integer polynomials to the reals that casts integer coefficients and evaluates the variable at b."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-positive-primitive-rational-polynomial"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.positivePrimitive"),
            H("positive primitive integer representative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a rational polynomial f, clear denominators by integerNormalization, take the integer primitive part, and normalize its leading sign. For nonzero f this gives a primitive integer polynomial with positive leading coefficient whose rational image is associated with f."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-rational-gcd"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualGcdQ"),
            H("gcd over the rational polynomial ring"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The normalized gcd in Q[b] of the rational images of actualMinorA0 and actualMinorC0."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-positive-primitive-gcd"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualPrimitiveGcd"),
            H("source positive primitive common factor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The positive primitive integer representative of actualGcdQ, implementing h=pp_+(gcd(a0,c0))."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-reduced-leading-minor"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedA"),
            H("exact reduced leading source minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational polynomial quotient actualMinorA0/actualPrimitiveGcd. The selected-source theorem proves exact factorization and that this quotient has integer coefficients."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-actual-reduced-constant-minor"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.actualReducedC"),
            H("exact reduced constant source minor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational polynomial quotient actualMinorC0/actualPrimitiveGcd, with exact factorization and integer coefficients supplied by the same theorem."))), DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("cubic-gain-selected-actual-normalized-source-lift"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/ActualMinorLift.selected_source_normalized_lift"),
            H("actual selected source-normalized lift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Without added hypotheses, h is primitive and has positive leading coefficient, and there exists a nonzero rational u with h mapped to Q[b] equal to u times the actual rational gcd. There exist integer polynomials A,C with a0=h A and c0=h C, whose rational images equal the exact quotients actualReducedA and actualReducedC. At criticalRoot, h and the reduced leading minor are nonzero, and liftedR(criticalRoot) equals minus the evaluation of actualReducedC divided by the evaluation of actualReducedA."))), DescribeRole.Theorem))));
}
