using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenChronologyFiberSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar prime-golden observation is constant on a bidegree fiber, while a noncommutative second-Magnus readout can separate chronology inside that fiber.",
        H("Prime-Golden Chronology Fiber Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-chronology-fiber-separation"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_chronology_fiber_separation"),
                H("Magnus separates swapped histories hidden by scalar observation"),
                StatementSource.FromAuthor(FiberSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A fixed-prime scalar endpoint factors through the prime-event and short-step bidegree, so every word in one bidegree fiber has the same complete scalar trajectory.")),
                    Paragraph(Text(
                        "A two-event word and its reversal share that bidegree and scalar trajectory.")),
                    Paragraph(Text(
                        "When the two oriented commutators differ, the degree-two Magnus coordinate distinguishes the reversed histories inside the same scalar fiber."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Word(params Formula[] letters)
    {
        var items = new List<Formula> { OpenBracket };
        for (var index = 0; index < letters.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(letters[index]);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }

    private static Formula FiberSeparationFormula()
    {
        Formula observe = F.Id("f");
        Formula u = F.Id("u");
        Formula w = F.Id("w");
        Formula fu = Call("f", u);
        Formula fw = Call("f", w);
        Formula uw = Word(u, w);
        Formula wu = Word(w, u);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, observe, Comma, Sp, Forall, Sp, u, Comma, Sp, Forall, Sp, w, Comma, Sp,
            Call("commutator", fu, fw), Sp, Neq, Sp, Call("commutator", fw, fu),
            Sp, Rightarrow, RowBreak, Grp(),
            Call("primeGoldenBidegree", uw), Sp, Eq, Sp, Call("primeGoldenBidegree", wu),
            Sp, Land, RowBreak, Grp(),
            Call("sameScalarTrajectory", uw, wu),
            Sp, Land, RowBreak, Grp(),
            Call("doubledMagnusDegreeTwo", Call("chronologicalSignature", observe, uw)),
            Sp, Neq, Sp,
            Call("doubledMagnusDegreeTwo", Call("chronologicalSignature", observe, wu)), Dot,
            End, Grp(F.Id("gathered"))));
    }

}
