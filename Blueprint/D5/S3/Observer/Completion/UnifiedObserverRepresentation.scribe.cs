using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class UnifiedObserverRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete protocol signature has a canonical quotient-range representation and three equivalent factorization tests.",
        H("Unified Observer Representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("unified-observer-representation"),
            DeclarationHandle.Create(
                "D5/S3/Observer/Completion/UnifiedObserverRepresentation.unified_observer_representation"),
            H("Canonical signature quotient and universal observer factorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The complete signature sends a source state to the protocol-indexed family "
                        + "of laws. Its equality-kernel quotient is canonically equivalent to the "
                        + "realized signature range, with the equivalence fixed on every state.")),
                Paragraph(Text(
                    "For an interface r, factorization of every protocol law through the realized "
                        + "interface image is equivalent to inclusion of the interface kernel in "
                        + "the complete-signature kernel. The same condition is equivalent to the "
                        + "unique map from the realized interface image into the signature image."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula fn, params Formula[] args)
    {
        var items = new List<Formula> { fn, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula x = F.Id("X");
        Formula protocol = F.Id("P");
        Formula lawType = F.Id("L");
        Formula interfaceType = F.Id("R");
        Formula law = F.Id("law");
        Formula r = F.Id("r");
        Formula p = F.Id("protocol");
        Formula state = F.Id("x");
        Formula statePrime = F.Id("y");
        Formula signature = Call("completeSignature", law);
        Formula signatureKernel = Call("ker", signature);
        Formula interfaceKernel = Call("ker", r);
        Formula signatureRange = Call("range", signature);
        Formula interfaceRange = Call("range", r);
        Formula quotient = Call("quotient", signatureKernel);
        Formula stateClass = Call("quotientClass", signatureKernel, state);
        Formula rangeFactorLaw = Call("rangeFactorization", signature);
        Formula rangeFactorR = Call("rangeFactorization", r);

        Formula lawFactor = Seq(
            Forall, Sp, Typed(p, protocol), Comma, Sp,
            Exists, Sp, F.Id("kProtocol"), Colon, Sp, new Formula.TypeArrow(interfaceRange, lawType), Comma, Sp,
            Apply(law, p), Sp, Eq, Sp, F.Id("kProtocol"), Sp, Circ, Sp, rangeFactorR);
        Formula kernelInclusion = Seq(
            Forall, Sp, Typed(state, x), Comma, Sp, Typed(statePrime, x), Comma, Sp,
            Apply(r, state), Sp, Eq, Sp, Apply(r, statePrime), Sp, Rightarrow, Sp,
            Apply(signature, state), Sp, Eq, Sp, Apply(signature, statePrime));
        Formula canonical = Seq(
            Exists, Bang, Sp, F.Id("E"), Colon, Sp,
            new Formula.TypeArrow(quotient, signatureRange), Comma, Sp,
            Forall, Sp, Typed(state, x), Comma, Sp,
            Apply(F.Id("E"), stateClass), Sp, Eq, Sp,
            Call("realizedPair", Apply(signature, state), Call("witness", state)));
        Formula imageFactor = Seq(
            Exists, Bang, Sp, F.Id("phi"), Colon, Sp,
            new Formula.TypeArrow(interfaceRange, signatureRange), Comma, Sp,
            rangeFactorLaw, Sp, Eq, Sp, F.Id("phi"), Sp, Circ, Sp, rangeFactorR);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(x, Comma, Sp, protocol, Comma, Sp, lawType, Comma, Sp, interfaceType), type),
            Comma, RowBreak, Grp(),
            Typed(law, new Formula.TypeArrow(protocol, new Formula.TypeArrow(x, lawType))), Comma, Sp,
            Typed(r, new Formula.TypeArrow(x, interfaceType)), Comma, RowBreak, Grp(),
            canonical, Sp, Land, RowBreak, Grp(),
            Open, lawFactor, Sp, Iff, Sp, kernelInclusion, Close, Sp, Land, RowBreak, Grp(),
            Open, kernelInclusion, Sp, Iff, Sp, imageFactor, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
