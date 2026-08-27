using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class FiniteDistinguishingCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite operational quotient admits a finite protocol certificate even for an infinite protocol family.",
        H("Finite Distinguishing Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-distinguishing-certificate"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/PredictionCertificates/FiniteDistinguishingCertificate."
                    + "finite_distinguishing_certificate"),
            H("Finite quotient classes have a finite separating protocol subfamily"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The available protocol family may be infinite. A finite class carrier and a "
                        + "surjective class map encode exactly when all available protocol readouts "
                        + "agree. Choosing one separating protocol for each pair of distinct classes "
                        + "produces a finite selected subfamily with the same kernel.")),
                Paragraph(Text(
                    "The selected family is therefore a finite certificate for the complete quotient, "
                        + "and its finiteness comes from the target class carrier rather than from the "
                        + "protocol syntax."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

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

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula x = F.Id("X");
        Formula protocol = F.Id("P");
        Formula observation = F.Id("O");
        Formula classes = F.Id("C");
        Formula evaluate = F.Id("out");
        Formula available = F.Id("Q");
        Formula classify = F.Id("q");
        Formula selected = F.Id("selected");
        Formula state = F.Id("x");
        Formula statePrime = F.Id("y");
        Formula p = F.Id("protocol");
        Formula agreement = Seq(
            Forall, Sp, Typed(p, protocol), Sp, InMacro, Sp, available, Comma, Sp,
            Apply(Apply(evaluate, p), state), Sp, Eq, Sp,
            Apply(Apply(evaluate, p), statePrime));
        Formula selectedAgreement = Seq(
            Forall, Sp, Typed(p, protocol), Sp, InMacro, Sp, selected, Comma, Sp,
            Apply(Apply(evaluate, p), state), Sp, Eq, Sp,
            Apply(Apply(evaluate, p), statePrime));
        Formula kernelEquivalence = Seq(
            Forall, Sp, Typed(Seq(state, Comma, Sp, statePrime), x), Comma, Sp,
            Apply(classify, state), Sp, Eq, Sp, Apply(classify, statePrime), Sp, Iff, Sp,
            agreement);
        Formula conclusion = Seq(
            Exists, Sp, selected, Colon, Sp, Call("Finset", protocol), Comma, RowBreak, Grp(),
            Open, Call("subset", selected, available), Sp, Land, Sp,
            Forall, Sp, Typed(Seq(state, Comma, Sp, statePrime), x), Comma, Sp,
            Apply(classify, state), Sp, Eq, Sp, Apply(classify, statePrime), Sp, Iff, Sp,
            selectedAgreement, Close, Dot);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(x, Comma, Sp, protocol, Comma, Sp, observation, Comma, Sp, classes), type),
            Comma, RowBreak, Grp(),
            OpenBracket, Call("Finite", classes), CloseBracket, Comma, RowBreak, Grp(),
            Typed(evaluate, new Formula.TypeArrow(protocol, new Formula.TypeArrow(x, observation))), Comma, Sp,
            Typed(available, Call("Set", protocol)), Comma, Sp,
            Typed(classify, new Formula.TypeArrow(x, classes)), Comma, Sp,
            Typed(F.Id("surjective"), Call("Surjective", classify)), Comma, RowBreak, Grp(),
            kernelEquivalence, Sp, Rightarrow, RowBreak, Grp(),
            conclusion,
            End, Grp(F.Id("gathered"))));
    }
}
