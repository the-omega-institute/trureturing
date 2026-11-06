using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class SalieSumDocument : IScribeDocumentDefinition
{
    private static Formula All(string variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Colon, domain, Comma, Sp, body);

    private static Formula Ambient(Formula body) => All("F", F.Id("Type"), Seq(
        OpenBracket, Call("Field", F.Id("F")), CloseBracket, Sp,
        OpenBracket, Call("Fintype", F.Id("F")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", F.Id("F")), CloseBracket, Sp, body));

    private static Formula Parameters(Formula body) => Ambient(
        All("psi", Call("AddChar", F.Id("F"), F.Id("Complex")),
            All("a", F.Id("F"), All("b", F.Id("F"), body))));

    private static Formula OddNontrivial => Seq(
        Call("ringChar", F.Id("F")), Neq, Sp, D(2), Sp, Land, Sp,
        F.Id("psi"), Neq, Sp, D(1));

    private static Formula Chi(Formula x) => Call("chi", F.Id("F"), x);
    private static Formula Gauss => Call("G", F.Id("F"), F.Id("psi"));
    private static Formula Root => Call("R", F.Id("F"), F.Id("psi"), F.Id("a"), F.Id("b"));
    private static Formula Salie => Call("S", F.Id("F"), F.Id("psi"), F.Id("a"), F.Id("b"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Salié reciprocal phases collapse to a quadratic stationary-root fiber, giving exact nonsquare cancellation and the uniform square-root bound over every odd finite field.",
        H("Salié sums and quadratic stationary fibers"),
        Blocks(
            Paragraph(Text("Let F be any finite field with a decidable equality, psi a complex additive character, and chi the integer-valued quadratic character transported to Complex. The notation chi(F,x), G(F,psi), R(F,psi,a,b), and S(F,psi,a,b) below denotes quadraticCharacterComplex x, quadraticGaussSum psi, quadraticRootPhase psi a b, and salieSum psi a b, respectively. The exact evaluation assumes odd characteristic, psi nontrivial, and b nonzero; a is unrestricted, including zero. The norm theorem also includes b zero.")),
            Paragraph(Text("The mechanism connects two actions. Multiplication by a unit t acts on additive phases by mulShift; the Gauss sum transforms with inverse multiplicative eigencharacter chi(t). Counting the square-map fibers identifies a quadratic exponential sum with that Gauss eigenspace. Completion of the square then converts a linear perturbation into a reciprocal phase. Additive Fourier orthogonality selects the single equation y squared equals 4ab. Thus the reciprocal phase sum collapses to at most two stationary roots. Nonsquares have no roots and cancel exactly.")),
            Paragraph(Text("This is the classical Salié evaluation, with no mathematical novelty claim. The proof reuses Mathlib's quadraticChar_card_sqrts, gaussSum_mulShift_eq, additive orthogonality sum_mulShift, gaussSum_sq, and nonvanishing of primitive Gauss sums. It constructs the Fourier-to-reciprocal reindexing in this module. No prime-field restriction, choice of a standard additive character, or extra nonzero assumption on a is imposed.")),
            Describe.Lean(
                DescribeId.Create("salie-complex-quadratic-character"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex"),
                H("The complex quadratic character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite field F, compose quadraticChar F with Int.castRingHom Complex as a multiplicative character. Its value at zero is zero and its values away from zero are one or minus one. The finite-field and decidable-equality parameters are the same throughout this document."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("salie-reciprocal-phase-sum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.salieSum"),
                H("The reciprocal phase sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex additive character psi and a,b in F, S(F,psi,a,b) is the sum over all x in F of chi(F,x) times psi(a*x+b*x inverse). The zero summand vanishes because chi(F,0)=0; Lean's total inverse therefore introduces no additional boundary term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("salie-quadratic-gauss-sum"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticGaussSum"),
                H("The quadratic Gauss sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex additive character psi, G(F,psi) is gaussSum quadraticCharacterComplex psi, the sum of chi(F,x)*psi(x) over x in F. In odd characteristic with psi nontrivial its square is chi(F,-1) times the field cardinality and its norm is the square root of that cardinality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("salie-stationary-root-phase"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase"),
                H("The stationary-root phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every psi and a,b in F, R(F,psi,a,b) is the finite sum of psi(y) over exactly those y in F satisfying y squared equals 4*a*b. Roots are counted once each, so the singular zero fiber contains just zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("salie-quadratic-character-cast"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticCharacterComplex_apply"),
                H("Character transport is the integer cast"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x in F, quadraticCharacterComplex x equals the complex cast of quadraticChar F x. This definitional, bind-only helper is consumed by the quadratic-phase calculation and the character coefficient in the reciprocal reindexing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-quadratic-root-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticRootFiber_card"),
                H("Counting stationary roots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If ringChar F differs from two, then for every a,b in F the integer cast of the cardinality of the root set equals quadraticChar F (4*a*b)+1. This is a bind-only application of Mathlib's square-root count. The private root-phase norm estimate consumes it to obtain the cardinality bound two, and the final Salié norm theorem consumes that estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-empty-root-phase"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticRootPhase_eq_zero_of_not_isSquare"),
                H("An empty stationary fiber contributes zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every psi,a,b, if 4*a*b is not a square, R(F,psi,a,b)=0. No odd-characteristic or nontrivial-character assumption is needed for this empty-sum statement. This bind-only helper is consumed by salieSum_eq_zero_of_not_isSquare."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-quadratic-phase-gauss"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.quadraticPhase_sum_eq"),
                H("A quadratic phase lies in the Gauss eigenspace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd finite field F, nontrivial complex additive character psi, and unit t of F, the sum of psi(t*x squared) over x equals chi(F,t) inverse times G(F,psi). Sum over fibers of x maps to x squared, replace each fiber cardinality by chi(F,z)+1, and eliminate the additive-character sum. Mathlib's Gauss shift law evaluates the remaining term. This bind-only combination of existing fiber and character identities is consumed by the private completed-square theorem, then by salieSum_fourier and the exact evaluation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-zero-right-boundary"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.salieSum_zero_right"),
                H("The boundary with zero reciprocal coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd finite field, every complex additive character psi, and every a, S(F,psi,a,0) is zero when a=0 and is chi(F,a)*G(F,psi) otherwise. This theorem does not require psi nontrivial. Nontriviality of the quadratic character handles a=0; the Gauss shift law handles a nonzero, and the character is its own inverse. This bind-only boundary calculation is consumed by salieSum_norm_le."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-exact-evaluation"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq"),
                H("Exact evaluation over every odd finite field"),
                StatementSource.FromAuthor(Disp(Parameters(Seq(
                    OddNontrivial, Sp, Land, Sp, F.Id("b"), Neq, Sp, D(0), Sp,
                    Implies, Sp, Salie, Eq, Chi(F.Id("b")), Cdot, Sp,
                    Gauss, Cdot, Sp, Root)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Additive orthogonality gives q*R as the sum over t of psi(-4abt) times Q(t), where Q(t) is the sum over y of psi(t*y squared+y). For t nonzero, translate y by the inverse of 2t and use quadraticPhase_sum_eq: Q(t)=chi(F,t) inverse times G times psi(-(4t) inverse). The t=0 term is explicitly zero because psi is nontrivial.")),
                    Paragraph(Text("The unit bijection t maps to -4bt converts this Fourier sum into chi(F,-b)*G*S. The character coefficient follows from chi(F,4)=1 and chi(F,-b) squared equal to one. Combine this relation with G squared equal to chi(F,-1)*q and cancel the nonzero coefficient to obtain the displayed evaluation. The live intermediate Fourier-to-reciprocal identity is the content-bearing construction; the theorem is not merely a root-count wrapper. Its consumers are the nonsquare theorem and the square branch of the norm theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-nonsquare-cancellation"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.salieSum_eq_zero_of_not_isSquare"),
                H("Nonsquare products cancel exactly"),
                StatementSource.FromAuthor(Disp(Parameters(Seq(
                    OddNontrivial, Sp, Land, Sp, F.Id("b"), Neq, Sp, D(0), Sp,
                    Land, Sp, Neg, Sp, Call("IsSquare", Seq(F.Id("a"), Cdot, Sp, F.Id("b"))), Sp,
                    Implies, Sp, Salie, Eq, D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If a*b is not a square and b is nonzero, the exact evaluation vanishes. A putative root of 4ab would yield a square root of ab after division by two. This bind-only consequence of the exact evaluation is consumed on the nonsquare branch of salieSum_norm_le."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("salie-uniform-square-root-bound"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SalieSum.salieSum_norm_le"),
                H("Uniform square-root cancellation"),
                StatementSource.FromAuthor(Disp(Parameters(Seq(
                    OddNontrivial, Sp, Implies, Sp,
                    Vert, Sp, Salie, Vert, Sp, Leq, Sp,
                    D(2), Cdot, Sp, Sqrt, Grp(Call("card", F.Id("F"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all a,b in every odd finite field and every nontrivial complex additive character, the complex norm of S is at most two times the real square root of the field cardinality. The Gauss-square identity and the unit norm of chi(-1) give norm G equal to square root q. Additive-character values have norm one, and the root-count formula bounds the stationary fiber by two. The triangle inequality then gives norm R at most two.")),
                    Paragraph(Text("The proof uses the boundary theorem when b=0, exact nonsquare cancellation when ab is a nonsquare, and the exact evaluation plus the root-phase estimate in the remaining branch. The estimate chain is the content-bearing conclusion; the cardinality and boundary helpers have genuine consumers. This is a uniform finite-field bound, without a claim of asymptotic sharpness or a broader research objective being completed."))),
                DescribeRole.Theorem))));
}
