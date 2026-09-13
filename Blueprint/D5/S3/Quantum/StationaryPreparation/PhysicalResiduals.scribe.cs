using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class PhysicalResidualsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact equal-phase output determines the actual normalized residual memories, including their phases.",
        H("Physical Residual Memories"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-residuals-of-preparation"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/PhysicalResiduals.actual_residuals_of_preparation"),
            H("Residuals extracted from a fixed physical preparation"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The alphabet sigma is finite and nonempty, and a assigns an arbitrary natural capacity " +
                    "to each letter, including zero. H is any finite-dimensional complex inner-product " +
                    "space. A PhysicalPreparation consists of one total linear isometry V from H to " +
                    "EuclideanSpace(Complex,sigma) tensor H, a unit initial vector, a common unit final " +
                    "vector, and an exact full-output equality. After sum(i,a(i)) emissions, the output " +
                    "is the uniform equal-phase occupation vector tensor the final vector. The final " +
                    "vector is not a prescribed reset. This model has one counted memory and fixed " +
                    "control throughout, with no postselection.")),
                Paragraph(Text(
                    "Box(a) contains all residual occupations r with 0 <= r(i) <= a(i). Write |r| for " +
                    "their sum and M(r)=|r|!/product(i,r(i)!). The occupation vector has coordinate " +
                    "1/sqrt(M(a)) on words of occupation a and zero elsewhere. Letter operators are " +
                    "the actual tensor components of V; wordOp composes them in chronological order. " +
                    "The tensor coordinate equivalence changes coordinates within H and adds no memory.")),
                Paragraph(Text(
                    "Choose a representative prefix with counts a-r and let phi(r) be its actual " +
                    "memory multiplied by sqrt(M(a)/M(r)). The conclusion NormalizedResiduals gives " +
                    "norm phi(r)=1, phi(0)=final, and phi(a)=initial. For every prefix w with counts " +
                    "a-r, its actual memory is sqrt(M(r)/M(a)) times phi(r), as an equality of complex " +
                    "vectors. For nonzero r, the i-th component of V phi(r) is " +
                    "sqrt(r(i)/|r|) times phi(r-e(i)) when r(i)>0, and zero otherwise. There is no " +
                    "transition assertion at the zero residual.")),
                Paragraph(Text(
                    "Continue two prefixes with the same remaining occupation through the same " +
                    "isometry. Every full-word coefficient is fixed by the exact output equation. " +
                    "The continuation preserves inner products and is injective, so the two prefix " +
                    "memories coincide, including phase. Summing squared continuation coefficients " +
                    "over the M(r) legal suffixes gives squared prefix norm M(r)/M(a). These two " +
                    "facts establish the normalization and the actual-prefix assertion. Appending " +
                    "one letter gives the stated guarded transition, using the multinomial erasure " +
                    "recurrence for its coefficient.")),
                Paragraph(Text(
                    "For capacities (4,2,1,1), the emission length is 8 and M(a)=8!/(4!2!1!1!)=840. " +
                    "The exact target therefore contains 840 words of amplitude 1/sqrt(840). " +
                    "All-zero capacities give the empty word and M(0)=1; the same extraction includes " +
                    "that boundary case."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula sigma = F.Id("sigma"), memory = F.Id("H"), a = F.Id("a"), p = F.Id("P");
        Formula v = Call("V", p), initial = Call("initial", p), final = Call("final", p);
        return Disp(Seq(
            Forall, Sp, sigma, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Fintype", sigma), Comma, Sp, Call("DecidableEq", sigma), Comma, Sp,
            Call("Nonempty", sigma), Comma, Esc,
            Forall, Sp, memory, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("NormedAddCommGroup", memory), Comma, Sp,
            Call("InnerProductSpace", F.Id("Complex"), memory), Comma, Sp,
            Call("FiniteDimensional", F.Id("Complex"), memory), Comma, Esc,
            Forall, Sp, a, Colon, Sp, sigma, Sp, To, Sp, F.Id("Nat"), Comma, Esc,
            Forall, Sp, p, Colon, Sp, Call("PhysicalPreparation", a, memory), Comma, Esc,
            Call("NormalizedResiduals", a, v, initial, final, Call("residual", a, v, initial))));
    }
}
