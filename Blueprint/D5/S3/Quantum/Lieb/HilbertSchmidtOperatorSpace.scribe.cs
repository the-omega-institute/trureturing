using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Lieb;

internal sealed class HilbertSchmidtOperatorSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed reusable operator API: HilbertSchmidtOperatorSpace.",
        H("HilbertSchmidtOperatorSpace"),
        Blocks(
            Paragraph(Text("Consumed Apache-2.0 Physlib source at immutable revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and "
                + "Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is "
                + "available in the repository-pinned Mathlib.")),
            Describe.Lean(
                DescribeId.Create("hs-left-right-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_rightMulHS_commute"),
                H("Left and right Hilbert-Schmidt multiplication commute"),
                StatementSource.FromAuthor(CommuteFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a finite-dimensional complex inner-product space. HSOp equips its "
                        + "bounded operators with Hilbert-Schmidt coordinates. Left multiplication sends T to A "
                        + "T, and right multiplication sends T to T B.")),
                    Paragraph(Text("These operators commute for arbitrary A,B by associativity. No A/B commutation, "
                        + "positivity, self-adjointness or nontriviality is assumed. This declaration omits "
                        + "completeness of the underlying carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hs-left-cfc"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_cfcR"),
                H("Real CFC commutes with left multiplication"),
                StatementSource.FromAuthor(CfcFormula(false)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a complete finite-dimensional complex Hilbert space. The exact "
                        + "statement also requires real CFC and nontriviality for its bounded-operator algebra. "
                        + "A is self-adjoint, and f is continuous on its real spectrum; no global continuity or "
                        + "positivity of A is required.")),
                    Paragraph(Text("Left multiplication by f(A) equals real CFC of the Hilbert-Schmidt "
                        + "left-multiplication operator of A. The left-multiplication star algebra homomorphism "
                        + "and finite-dimensional continuity supply the bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hs-right-cfc"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.rightMulHS_cfcR"),
                H("Real CFC commutes with right multiplication"),
                StatementSource.FromAuthor(CfcFormula(true)),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Divergence/tsukamotomoriyamasaki2026lieb")),
                Blocks(
                    Paragraph(Text("The carrier is a complete finite-dimensional complex Hilbert space. The exact "
                        + "statement requires real CFC for both its bounded-operator algebra and the opposite "
                        + "algebra, and nontriviality of the bounded-operator algebra. A is self-adjoint and f "
                        + "is continuous on its real spectrum.")),
                    Paragraph(Text("Right multiplication by f(A) equals real CFC of the Hilbert-Schmidt "
                        + "right-multiplication operator of A. The opposite-algebra star homomorphism handles "
                        + "reversed multiplication; original A and B need not commute."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)) };
        if (arguments.Length == 0) return Seq([.. items]);
        items.Add(Open);
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Instance(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula U => F.Id("u");
    private static Formula Carrier => F.Id("H");
    private static Formula Operators => Call("L", Carrier);
    private static Formula RealFunction => Seq(RealType, Sp, To, Sp, RealType);
    private static Formula HilbertPrefix(bool nontrivial = true, bool finite = false,
        bool complete = true)
    {
        var items = new List<Formula> {
            Forall, Sp, U, Colon, Sp, Call("Level"), Comma, Esc,
            Carrier, Colon, Sp, Call("Type", U), Comma, Esc,
            Instance("NormedAddCommGroup", Carrier), Comma, Sp,
            Instance("InnerProductSpace", ComplexType, Carrier), Comma, Sp };
        if (complete) items.AddRange([Instance("CompleteSpace", Carrier), Comma, Sp]);
        if (nontrivial) items.AddRange([Instance("Nontrivial", Carrier), Comma, Sp]);
        if (finite) items.AddRange([Instance("FiniteDimensional", ComplexType, Carrier), Comma, Sp]);
        return Seq([.. items]);
    }
    private static Formula Conjunction(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clauses[i]);
        }
        return Seq([.. items]);
    }

    private static Formula CommuteFormula() => Disp(Seq(
        HilbertPrefix(nontrivial: false, finite: true, complete: false),
        F.Id("A"), Comma, Sp, F.Id("B"), Colon, Sp, Operators, Comma, Esc,
        Call("Commute", Call("leftMulHS", Carrier, F.Id("A")),
            Call("rightMulHS", Carrier, F.Id("B"))), Dot));
    private static Formula CfcFormula(bool right)
    {
        Formula a = F.Id("A"), f = F.Id("f");
        string multiplication = right ? "rightMulHS" : "leftMulHS";
        Formula oppositeCfc = right ? Seq(
            Instance("ContinuousFunctionalCalculus", RealType, Call("MulOpposite", Operators),
                Call("IsSelfAdjoint")), Comma, Sp) : Seq();
        return Disp(Seq(HilbertPrefix(nontrivial: false, finite: true),
            Instance("ContinuousFunctionalCalculus", RealType, Operators,
                Call("IsSelfAdjoint")), Comma, Sp, oppositeCfc,
            Instance("Nontrivial", Operators), Comma, Esc,
            f, Colon, Sp, RealFunction, Comma, Sp, a, Colon, Sp, Operators, Comma, Esc,
            Conjunction(Call("IsSelfAdjoint", a),
                Call("ContinuousOn", f, Call("spectrum", RealType, a))),
            Sp, Implies, Sp,
            Call(multiplication, Carrier, Call("cfcR", Carrier, f, a)), Sp, Eq, Sp,
            Call("cfcR", Call("HSOp", Carrier), f,
                Call(multiplication, Carrier, a)), Dot));
    }
}
