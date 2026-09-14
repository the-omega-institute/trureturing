using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class HeadAttainmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed complex linear isometry exactly prepares every finite occupation state with minimum memory.",
        H("Stationary Occupation Attainment"),
        Blocks(Describe.Lean(
            DescribeId.Create("stationary-attainment"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/StationaryPreparation/HeadAttainment.stationary_attainment"),
            H("Exact preparation at the minimum dimension"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/qiclean2026gramunitary")),
            Blocks(
                Paragraph(Text(
                    "For every finite nonempty alphabet sigma and every natural capacity function a, " +
                    "choose a head h attaining max(i,a(i)). The memory H is the span of the explicit " +
                    "head Gram vectors chi(r). There exists a PhysicalPreparation on H, and its complex " +
                    "dimension is product(i,a(i)+1)-max(i,a(i)). The lower bound applies to every " +
                    "PhysicalPreparation in this model, so this dimension is the least admissible one.")),
                Paragraph(Text(
                    "For each nonzero r, prescribe the emission image whose letter i component is " +
                    "chi(r-e(i)) when r(i)>0 and zero otherwise. The head Gram recurrence proves " +
                    "equality of the source and image Gram matrices. Embed the source into one letter " +
                    "coordinate of the output space and apply the equal-Gram unitary extension. " +
                    "The resulting V is one total complex linear isometry from H to " +
                    "EuclideanSpace(Complex,sigma) tensor H. It preserves every linear relation " +
                    "among the residual vectors and is reused unchanged at every emission.")),
                Paragraph(Text(
                    "Normalize by phi(r)=chi(r)/sqrt(M(r)). The Gram diagonal proves unit norm. " +
                    "The identity |r| M(r-e(i))=r(i) M(r) converts the raw transition into Step: " +
                    "the letter i component of V phi(r) is sqrt(r(i)/|r|) phi(r-e(i)) for r(i)>0 " +
                    "and zero otherwise. The word evolution formula then gives every allowed " +
                    "length-|a| word the same positive amplitude 1/sqrt(M(a)), and every other " +
                    "word amplitude zero. The initial vector is phi(a), and every allowed word " +
                    "has the common unit final vector phi(0). Hence emitted(V,|a|,phi(a)) equals " +
                    "sector(a) tensor phi(0) exactly.")),
                Paragraph(Text(
                    "When all capacities vanish, the span has dimension one, the initial and final " +
                    "vectors agree, and there are zero emissions. A singleton alphabet, zero " +
                    "coordinates, and tied maxima are included. No clock, varying gate, postselection, " +
                    "or extra memory is part of the construction. The final vector is freely chosen " +
                    "by the construction and is not required to equal a prescribed reset vector."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a = F.Id("a"), h = F.Id("h"), p = F.Id("P");
        Formula memory = Call("H", a, h);
        Formula bound = Seq(Call("product", Call("aPlusOne", a)), Sp, Minus, Sp,
            Call("max", a));
        return Disp(Seq(Forall, Sp, a, Colon, Sp, F.Id("sigma"), Sp, To, Sp, F.Id("Nat"), Comma, Esc,
            Exists, Sp, h, Colon, Sp, F.Id("sigma"), Comma, Sp,
            Exists, Sp, p, Colon, Sp, Call("PhysicalPreparation", memory, a), Comma, Esc,
            Call("finrank", F.Id("Complex"), memory), Sp, Eq, Sp, bound));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
