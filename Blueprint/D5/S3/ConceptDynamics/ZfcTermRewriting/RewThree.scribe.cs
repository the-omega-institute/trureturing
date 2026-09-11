using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcTermRewriting;

internal sealed class RewThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed Foundation.Syntax.Predicate.Rew source selected from the historical first-order pair extension.",
        H("RewThree"),
        Blocks(
            Paragraph(Text(
                "This document mirrors the retained declarations from Foundation.Syntax.Predicate.Rew, "
                    + "lines 638-953, at Foundation revision 30a16ffa93d79d73ab4d02427fa00f50e039bf29. "
                    + "The excerpt records the term-rewriting laws and interfaces associated with the concrete "
                    + "first-order pair extension; current downstream consumer usage has not been re-queried.")),
            Paragraph(Text(
                "The immutable source map, modification notices, full Apache-2.0 license and retirement "
                    + "condition are in Library/ConceptDynamics/foundation2026firstorder.md.")),
            DescribeEntry(
                "fixitr-bvar",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_bvar",
                "Fixing bound variables preserves the variable with an enlarged finite index",
                FixitrBvarFormula(),
                "For every finite bound index x, fixing m variables maps the bound variable to its "
                    + "castAdd representative in the enlarged context.",
                DescribeRole.Lemma),
            DescribeEntry(
                "fixitr-fvar",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.fixitr_fvar",
                "Fixing free variables either binds or shifts them",
                FixitrFvarFormula(),
                "A free variable below the fixed prefix becomes a bound variable; otherwise its index "
                    + "is decreased by the prefix length.",
                DescribeRole.Lemma),
            DescribeEntry(
                "rew-eq-of-fun-eq-on",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.rew_eq_of_funEqOn",
                "Rewrites agree when they agree on the variables visible in a term",
                RewEqFormula(),
                "Agreement on every bound variable and on the free variables occurring in the term "
                    + "is sufficient for equality after rewriting that term.",
                DescribeRole.Lemma),
            DescribeEntry(
                "lmap-bind",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bind",
                "Language maps commute with term binding",
                LMapBindFormula(),
                "Mapping function symbols through a language homomorphism commutes with binding both "
                    + "bound and free variables.",
                DescribeRole.Lemma),
            DescribeEntry(
                "lmap-map",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_map",
                "Language maps commute with variable maps",
                LMapMapFormula(),
                "The map that changes variable indices and free-variable labels commutes with the "
                    + "language map on terms.",
                DescribeRole.Lemma),
            DescribeEntry(
                "lmap-bshift",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.lMap_bShift",
                "Language maps commute with bound-variable shifting",
                LMapBShiftFormula(),
                "Adding one bound-variable slot before or after a language map gives the same term.",
                DescribeRole.Lemma),
            DescribeEntry(
                "fvar-rew",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_rew",
                "A free variable after rewriting comes from a source variable (the canonical selector is RewThreeCompat.fvar_rew; the source name is fvar?_rew).",
                FVarRewFormula(),
                "If a free variable occurs in a rewritten term, it came either from a rewritten bound "
                    + "variable or from a free variable of the source term.",
                DescribeRole.Lemma),
            DescribeEntry(
                "fvar-bshift",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift",
                "Bound-variable shifting preserves free-variable support (the canonical selector is RewThreeCompat.fvar_bShift; the source name is fvar?_bShift).",
                FVarBShiftFormula(),
                "The bShift operation changes only bound indices, so the set of free variables is "
                    + "unchanged.",
                DescribeRole.Lemma),
            DescribeEntry(
                "to-empty",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.toEmpty",
                "A term with no free variables is converted to an empty-variable term",
                ToEmptyFormula(),
                "A closed semiterm is recursively retyped as a ClosedSemiterm; the free-variable case "
                    + "is impossible under the empty support hypothesis.",
                DescribeRole.Definition),
            DescribeEntry(
                "emb-to-empty",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.emb_toEmpty",
                "Embedding the empty-variable form recovers the original term",
                EmbToEmptyFormula(),
                "Embedding the term produced by toEmpty is definitionally equal to the original term.",
                DescribeRole.Lemma),
            DescribeEntry(
                "rewriting",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.Rewriting",
                "A rewriting action applies rewrites to formulas and respects quantifiers",
                RewritingFormula(),
                "A Rewriting instance supplies an action of term rewrites on formulas, with universal "
                    + "and existential quantification transported through the rewrite.",
                DescribeRole.Definition),
            DescribeEntry(
                "reflective-rewriting",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.ReflectiveRewriting",
                "The identity rewrite acts as the identity on formulas",
                ReflectiveFormula(),
                "Reflectivity records that applying Rew.id leaves every formula unchanged.",
                DescribeRole.Definition),
            DescribeEntry(
                "transitive-rewriting",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.TransitiveRewriting",
                "Composed rewrites act by successive formula application",
                TransitiveFormula(),
                "Transitivity identifies application of a composed rewrite with applying the first "
                    + "rewrite and then the second.",
                DescribeRole.Definition),
            DescribeEntry(
                "inj-map-rewriting",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.InjMapRewriting",
                "Injective variable and label maps induce an injective formula action",
                InjMapFormula(),
                "If both the bound-variable map and free-variable map are injective, the induced map "
                    + "on formulas is injective.",
                DescribeRole.Definition),
            DescribeEntry(
                "lawful-syntactic-rewriting",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.LawfulSyntacticRewriting",
                "Lawful syntactic rewriting combines identity, composition and injectivity",
                LawfulFormula(),
                "The lawful syntactic interface packages reflective, transitive and injective "
                    + "rewriting for the same syntactic formula family.",
                DescribeRole.Definition),
            DescribeEntry(
                "shift-conj-two",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shift_conj_two",
                "Shifting a conjunction shifts each formula (the canonical selector is RewThreeCompat.shift_conj_two; the source name is shift_conj₂).",
                ShiftConjFormula(),
                "The shift of a finite conjunction is the conjunction of the shifted list, including "
                    + "the empty and singleton cases.",
                DescribeRole.Lemma),
            DescribeEntry(
                "app-subst-fbar-zero-comp-shift-eq-free",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free",
                "Substituting the first free variable after shifting is free",
                AppSubstFormula(),
                "For a one-variable formula, shifting and substituting the zero free variable agrees "
                    + "with the free operation.",
                DescribeRole.Lemma))));

    private static DocumentBlock DescribeEntry(
        string id,
        string handle,
        string title,
        Formula formula,
        string narrative,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(handle),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(narrative))),
            role);

    private static Formula FixitrBvarFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("n"), Comma, Sp, F.Id("m"), Comma, Sp, F.Id("x"), InMacro, Sp,
            Call("Fin", F.Id("n")), Comma, Sp,
            Call("fixitr", F.Id("n"), F.Id("m"), Call("bvar", F.Id("x"))), Sp, Eq, Sp,
            Call("bvar", Call("castAdd", F.Id("x"), F.Id("m"))), Dot));

    private static Formula FixitrFvarFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("n"), Comma, Sp, F.Id("m"), Comma, Sp, F.Id("x"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("fixitr", F.Id("n"), F.Id("m"), Call("fvar", F.Id("x"))), Sp, Eq, Sp,
            Call("if", Call("lt", F.Id("x"), F.Id("m")),
                Call("bvar", Call("natAdd", F.Id("n"), Call("pair", F.Id("x"), Call("proof", F.Id("x"), F.Id("m"))))),
                Call("fvar", Subtract(F.Id("x"), F.Id("m")))), Dot));

    private static Formula RewEqFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("omega1"), Comma, Sp, F.Id("omega2"), Comma, Sp, F.Id("t"), Sp,
            Open, Call("agreeBvar", F.Id("omega1"), F.Id("omega2")), Sp, Land, Sp,
            Call("agreeOn", Call("fvarSupport", F.Id("t")), F.Id("omega1"), F.Id("omega2")), Close,
            Sp, Rightarrow, Sp, Call("eq", Call("apply", F.Id("omega1"), F.Id("t")), Call("apply", F.Id("omega2"), F.Id("t"))), Dot));

    private static Formula LMapBindFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("phi"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("e"), Comma, Sp, F.Id("t"), Sp,
            Call("lMap", F.Id("phi"), Call("bind", F.Id("b"), F.Id("e"), F.Id("t"))), Sp, Eq, Sp,
            Call("bind", Call("compose", Call("lMap", F.Id("phi")), F.Id("b")), Call("compose", Call("lMap", F.Id("phi")), F.Id("e")), Call("lMap", F.Id("phi"), F.Id("t"))), Dot));

    private static Formula LMapMapFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("phi"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("e"), Comma, Sp, F.Id("t"), Sp,
            Call("lMap", F.Id("phi"), Call("map", F.Id("b"), F.Id("e"), F.Id("t"))), Sp, Eq, Sp,
            Call("map", F.Id("b"), F.Id("e"), Call("lMap", F.Id("phi"), F.Id("t"))), Dot));

    private static Formula LMapBShiftFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("phi"), Comma, Sp, F.Id("t"), Sp,
            Call("lMap", F.Id("phi"), Call("bShift", F.Id("t"))), Sp, Eq, Sp,
            Call("bShift", Call("lMap", F.Id("phi"), F.Id("t"))), Dot));

    private static Formula FVarRewFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("omega"), Comma, Sp, F.Id("t"), Comma, Sp, F.Id("x"), Sp,
            Call("fvarAt", Call("apply", F.Id("omega"), F.Id("t")), F.Id("x")), Sp, Rightarrow, Sp,
            Open, Exists, Sp, F.Id("i"), Comma, Sp, Call("fvarAt", Call("apply", F.Id("omega"), Call("bvar", F.Id("i"))), F.Id("x")), Sp,
            Lor, Sp, Exists, Sp, F.Id("z"), Comma, Sp,
            Open, Call("contains", Call("fvarSupport", F.Id("t")), F.Id("z")), Sp, Land, Sp,
            Call("fvarAt", Call("apply", F.Id("omega"), Call("fvar", F.Id("z"))), F.Id("x")), Close, Close, Dot));

    private static Formula FVarBShiftFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("t"), Comma, Sp, F.Id("x"), Sp,
            Call("fvarAt", Call("bShift", F.Id("t")), F.Id("x")), Sp, Leftrightarrow, Sp,
            Call("fvarAt", F.Id("t"), F.Id("x")), Dot));

    private static Formula ToEmptyFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("t"), Sp, Call("freeVariables", F.Id("t")), Sp, Eq, Sp, Emptyset, Sp,
            Rightarrow, Sp, Call("toEmpty", F.Id("t")), Sp, InMacro, Sp, Call("ClosedSemiterm"), Dot));

    private static Formula EmbToEmptyFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("t"), Sp,
            Call("freeVariables", F.Id("t")), Sp, Eq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Call("emb", Call("toEmpty", F.Id("t"))), Sp, Eq, Sp, F.Id("t"), Dot));

    private static Formula RewritingFormula() =>
        Disp(Seq(
            Call("Rewriting", F.Id("L"), F.Id("xi"), F.Id("F"), F.Id("zeta"), F.Id("G")), Sp, Eq, Sp,
            Call("app", Call("Rew", F.Id("L"), F.Id("xi"), F.Id("n1"), F.Id("zeta"), F.Id("n2")), Call("F", F.Id("n1"))), Sp,
            Land, Sp, Call("app", F.Id("omega"), Call("forall", F.Id("phi"))), Sp, Eq, Sp,
            Call("forall", Call("app", Call("q", F.Id("omega")), F.Id("phi"))), Sp,
            Land, Sp, Call("app", F.Id("omega"), Call("exists", F.Id("phi"))), Sp, Eq, Sp,
            Call("exists", Call("app", Call("q", F.Id("omega")), F.Id("phi"))), Dot));

    private static Formula ReflectiveFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("phi"), Sp, Call("app", Call("id", F.Id("L")), F.Id("phi")), Sp, Eq, Sp, F.Id("phi"), Dot));

    private static Formula TransitiveFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("omega12"), Comma, Sp, F.Id("omega23"), Comma, Sp, F.Id("phi"), Sp,
            Call("app", Call("comp", F.Id("omega23"), F.Id("omega12")), F.Id("phi")), Sp, Eq, Sp,
            Call("app", F.Id("omega23"), Call("app", F.Id("omega12"), F.Id("phi"))), Dot));

    private static Formula InjMapFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("b"), Comma, Sp, F.Id("f"), Sp,
            Open, Call("Injective", F.Id("b")), Sp, Land, Sp, Call("Injective", F.Id("f")), Close,
            Sp, Rightarrow, Sp, Call("Injective", Call("mapAction", F.Id("b"), F.Id("f"))), Dot));

    private static Formula LawfulFormula() =>
        Disp(Seq(
            Call("LawfulSyntacticRewriting", F.Id("L"), F.Id("S")), Sp, Eq, Sp,
            Call("ReflectiveRewriting", F.Id("L"), F.Id("S")), Sp, Land, Sp,
            Call("TransitiveRewriting", F.Id("L"), F.Id("S")), Sp, Land, Sp,
            Call("InjMapRewriting", F.Id("L"), F.Id("S")), Dot));

    private static Formula ShiftConjFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("gamma"), Sp,
            Call("shift", Call("conj", F.Id("gamma"))), Sp, Eq, Sp,
            Call("conj", Call("map", Call("shift"), F.Id("gamma"))), Dot));

    private static Formula AppSubstFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("phi"), Colon, Sp, Call("S", D(1)), Comma, Sp,
            Call("subst", Call("shift", F.Id("phi")), Call("fvar", D(0))), Sp, Eq, Sp,
            Call("free", F.Id("phi")), Dot));
}
