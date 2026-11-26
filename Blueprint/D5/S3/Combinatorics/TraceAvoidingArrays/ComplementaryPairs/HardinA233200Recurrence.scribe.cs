using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233200RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233200Recurrence";
    private const string Note = "D5/L/Automata/hardin2013a233200";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's signed recurrence for the literal eight-colour width-six array count.",
        H("The recurrence at every height from 24"),
        Blocks(
            Describe.Lean(DescribeId.Create("lag-coefficient"), DeclarationHandle.Create(Owner + ".lagCoefficient"),
                H("Signed lag coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("In the following tuple, entry zero multiplies the height-one lag, "
                    + "and entry twenty-one multiplies the height-twenty-two lag.")),
                    Paragraph(Text("2624, -2916352, 2023751680, " 
                        + "-1022873305088, 396210733056000, -117075448369774592, " 
                        + "24978582014512857088, -3235719238675389743104, 32228191279027496943616, " 
                        + "79127659192314522138312704, -14330945495506960134011092992, 573127552562903399144703918080, " 
                        + "175763191005253023447780744495104, -41436012082310191504073111849926656, 7185129802334419767282615543889133568, " 
                        + "-1237277610717122610430160500786185895936, 170446905899499762382455179339748584980480, -17499361001276181422067502561786112042336256, " 
                        + "1430383734999503249937564429831586312219525120, -95447189449711067045772874206934987245596180480, 4407340875076004112707987073660040981149921574912, " 
                        + "-93536104789177786765035829293842113257979682750464."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + ".result"),
                H("Exact width-six recurrence"), StatementSource.FromAuthor(Disp(Recurrence())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(
                    Paragraph(Text("Here a is the literal cardinality from HardinA233200PairTransfer. "
                        + "The count uses the zero upper-left entry, the three contained bond directions, "
                        + "the exclusion of equal or complementary endpoints and all strict row-major first-use constraints.")),
                    Paragraph(Text("For each of the 58 source states the proof accumulates exact next-row weights by "
                        + "destination and checks the resulting row against the transition table. "
                        + "It verifies the constant-one vector and every next continuation vector through power 23.")),
                    Paragraph(Text("The power-23 vector equals the signed sum of powers 22 down to 1 in lag order. "
                        + "TransferMatrix.scalarRelationShift propagates the relation to every later power. "
                        + "The all-height counting bridge applies the anchored initial vector and shifts from "
                        + "additional rows to total height. At height 24 the lagged counts run from height 23 down to 2."))),
                DescribeRole.Theorem))));

    private static Formula Recurrence()
    {
        var n = F.Id("n");
        var j = F.Id("j");
        var height = Call("val", n);
        var lag = new Formula.Binary(Call("val", j), FormulaBinaryOperator.Add, D(1));
        var lower = new Formula.Binary(height, FormulaBinaryOperator.Subtract, lag);
        var term = new Formula.Binary(Call("lagCoefficient", j), FormulaBinaryOperator.Multiply, Count(lower));
        var sum = Seq(Sum, Underscore, Grp(j, Colon, Sp, Call("Fin", D(2,2))), Sp, term);
        return Seq(Forall, Sp, n, Colon, Sp, Name("PNat"), Comma, Sp,
            D(2,4), Sp, Le, Sp, height, Sp, Implies, Sp, Count(n), Sp, F.Eq, Sp, sum);
    }

    private static Formula Count(Formula n) => Seq(Open, Call("a", n), Colon, Sp, Name("Int"), Close);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, Formula value) => new Formula.Apply(Name(name), [value]);
}
