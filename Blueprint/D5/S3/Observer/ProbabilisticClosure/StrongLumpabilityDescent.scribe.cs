using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class StrongLumpabilityDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stochastic readout descends exactly when its pushed-forward one-step laws are constant on interface fibers.",
        H("Strong Lumpability Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strong-lumpability-descent-tfae"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent."
                        + "strong_lumpability_descent_tfae"),
                H("Strong lumpability is equivalent to stochastic descent"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state-conditioned PMF K(x) is pushed forward along the canonical "
                            + "realized-image readout of q. A descended Markov kernel is a function "
                            + "from that effective image to PMFs on the same image.")),
                    Paragraph(Text(
                        "The second clause is strong lumpability: equal q-values give equal "
                            + "one-step observed laws. The third clause states the same condition "
                            + "on the subtype-valued canonical readout, making the image carrier "
                            + "explicit.")),
                    Paragraph(Text(
                        "The proof constructs the descended row by choosing a preimage through "
                            + "the surjective canonical readout and proves independence of that "
                            + "choice from the fiber law."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Statement()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("B");
        Formula readout = F.Id("q");
        Formula rows = F.Id("K");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula pmf = Seq(Operatorname, Grp(F.Id("PMF")));
        Formula pmfMap = Seq(F.Id("PMF"), Dot, F.Id("map"));
        Formula image = Apply(Seq(Operatorname, Grp(F.Id("range"))), readout);
        Formula imagePmf = Apply(pmf, image);
        Formula statePmf = Apply(pmf, state);
        Formula canonical = Apply(F.Id("realizedReadout"), readout);
        Formula pushed = Apply(pmfMap, canonical, Apply(rows, x));
        Formula kernel = F.Id("kernel");
        Formula descended = Seq(
            Exists, Sp, kernel, Colon, Sp, Arrow(image, imagePmf), Comma, Sp,
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(pmfMap, canonical, Apply(rows, x)), Sp, Eq, Sp,
            Apply(kernel, Apply(canonical, x)));
        Formula qFiber = Seq(readout, Open, x, Close, Sp, Eq, Sp,
            readout, Open, y, Close);
        Formula imageFiber = Seq(canonical, Open, x, Close, Sp, Eq, Sp,
            canonical, Open, y, Close);
        Formula law = Seq(pushed, Sp, Eq, Sp,
            Apply(pmfMap, canonical, Apply(rows, y)));
        Formula clauses = Grp(OpenBracket,
            descended, Comma, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            qFiber, Sp, Rightarrow, Sp, law, Comma, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            imageFiber, Sp, Rightarrow, Sp, law,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma, RowBreak, Grp(),
            readout, Colon, Sp, Arrow(state, output), Comma, Sp,
            rows, Colon, Sp, Arrow(state, statePmf), Comma, RowBreak, Grp(),
            Call("ListTFAE", clauses), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        DefinitionDsl.Call(name, arguments);
}
