using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcTermRewriting;

internal sealed class RewThreeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Foundation =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/foundation2026firstorder");

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
                DescribeRole.Lemma,
                false),
            DescribeEntry(
                "fvar-bshift",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.fvar_bShift",
                "Bound-variable shifting preserves free-variable support (the canonical selector is RewThreeCompat.fvar_bShift; the source name is fvar?_bShift).",
                FVarBShiftFormula(),
                "The bShift operation changes only bound indices, so the set of free variables is "
                    + "unchanged.",
                DescribeRole.Lemma,
                false),
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
                "The retained structural induction proves that embedding the term produced by toEmpty recovers the original term.",
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
                "rewriting-subst",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.subst",
                "Formula substitution is the substitution rewrite action",
                SubstFormula(),
                "The formula-level substitution abbreviation applies Rew.subst to a formula through the Rewriting action.",
                DescribeRole.Definition),
            DescribeEntry(
                "rewriting-shift",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shift",
                "Formula shift is the shift rewrite action",
                ShiftFormula(),
                "The shift connective homomorphism applies Rew.shift to formulas while increasing free-variable indices.",
                DescribeRole.Definition),
            DescribeEntry(
                "rewriting-free",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.free",
                "Formula free operation removes the first free-variable slot",
                FreeFormula(),
                "The free connective homomorphism applies Rew.free from the n+1 free-variable family to the n family.",
                DescribeRole.Definition),
            DescribeEntry(
                "rewriting-shifts",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.shifts",
                "Formula-list shift maps each member",
                ShiftsFormula(),
                "The shifts definition maps the shift homomorphism over a finite list of formulas.",
                DescribeRole.Definition),
            DescribeEntry(
                "rewriting-shifts-nil",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_nil",
                "Shifting an empty formula list stays empty",
                ShiftsNilFormula(),
                "The ASCII compatibility selector forwards the source shifts_nil theorem, including its exact LCWQ and Rewriting assumptions.",
                DescribeRole.Lemma,
                false),
            DescribeEntry(
                "rewriting-shifts-cons",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_cons",
                "Shifting a cons list shifts its head and tail",
                ShiftsConsFormula(),
                "The ASCII compatibility selector forwards the source shifts_cons theorem pointwise over the head and tail.",
                DescribeRole.Lemma,
                false),
            DescribeEntry(
                "rewriting-shifts-neg",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.shifts_neg",
                "Shifting a negated formula list commutes with negation",
                ShiftsNegFormula(),
                "The ASCII compatibility selector forwards the source shifts_neg theorem for list negation.",
                DescribeRole.Lemma,
                false),
            DescribeEntry(
                "rewriting-emb",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.emb",
                "Empty-label formulas embed as connective homomorphisms",
                EmbFormula(),
                "The ASCII compatibility selector exposes the source emb connective homomorphism from an empty-label family O to a ξ-labelled family F.",
                DescribeRole.Definition,
                false),
            DescribeEntry(
                "subst-notation",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.substNotation",
                "Slash syntax expands to formula substitution",
                SubstNotationFormula(),
                "The ASCII parser selector mirrors the source substNotation macro: φ/[w] expands to φ ⇜ ![w].",
                DescribeRole.Definition,
                false),
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
                DescribeRole.Lemma,
                false),
            DescribeEntry(
                "app-subst-fbar-zero-comp-shift-eq-free",
                "D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat.app_subst_fbar_zero_comp_shift_eq_free",
                "Substituting the first free variable after shifting is free",
                AppSubstFormula(),
                "For a one-variable formula, shifting and substituting the zero free variable agrees "
                    + "with the free operation.",
                DescribeRole.Lemma,
                false))));

    private static DocumentBlock DescribeEntry(
        string id,
        string handle,
        string title,
        Formula formula,
        string narrative,
        DescribeRole role,
        bool upstream = true) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(handle),
            H(title),
            StatementSource.FromAuthor(formula),
            upstream
                ? AssessedProvenance.FromLiterature(Foundation)
                : AssessedProvenance.FromRepo(),
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
            Open,
            Open, Exists, Sp, F.Id("i"), Colon, Sp, Call("Fin", F.Id("n1")), Comma, Sp,
            Call("fvarAt", Call("apply", F.Id("omega"), Call("bvar", F.Id("i"))), F.Id("x")), Close,
            Sp, Lor, Sp,
            Open, Exists, Sp, F.Id("z"), Colon, Sp, F.Id("xi1"), Comma, Sp,
            Open, Call("contains", Call("fvarSupport", F.Id("t")), F.Id("z")), Sp, Land, Sp,
            Call("fvarAt", Call("apply", F.Id("omega"), Call("fvar", F.Id("z"))), F.Id("x")), Close, Close,
            Close, Dot));

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

    private static Formula RewritingFormula()
    {
        Formula l = F.Id("L"), xi = F.Id("xi"), zeta = F.Id("zeta");
        Formula n1 = F.Id("n1"), n2 = F.Id("n2");
        Formula omega = F.Id("omega12"), phi = F.Id("phi");
        Formula rew = Call("Rew", l, xi, n1, zeta, n2);
        Formula source = Call("F", n1), target = Call("G", n2);
        Formula appType = new Formula.TypeArrow(rew, Call("Hom", source, target));
        Formula appField = Seq(F.Id("app"), Colon, Sp, appType);
        Formula allLaw = Seq(
            F.Id("appAll"), Sp, omega, Comma, Sp, phi, Sp, Colon, Sp,
            Call("app", omega, Call("forall1", phi)), Sp, Eq, Sp,
            Call("forall1", Call("app", Call("q", omega), phi)));
        Formula exsLaw = Seq(
            F.Id("appExs"), Sp, omega, Comma, Sp, phi, Sp, Colon, Sp,
            Call("app", omega, Call("exists1", phi)), Sp, Eq, Sp,
            Call("exists1", Call("app", Call("q", omega), phi)));
        Formula quantifierScope = Seq(
            Forall, Sp, omega, Colon, Sp, rew, Comma, Sp,
            phi, Colon, Sp, source, Comma, Sp,
            allLaw, Sp, Land, Sp, exsLaw);
        return Disp(Seq(
            Call("Rewriting", l, xi, F.Id("F"), zeta, F.Id("G")), Sp, Eq, Sp,
            Open, appField, Comma, Sp, quantifierScope, Close, Dot));
    }

    private static Formula SubstFormula() =>
        Disp(Seq(
            F.Id("subst"), Colon, Sp,
            new Formula.TypeArrow(
                Call("F", F.Id("n1")),
                new Formula.TypeArrow(
                    new Formula.TypeArrow(
                        Call("Fin", F.Id("n1")),
                        Call("Semiterm", F.Id("L"), F.Id("xi"), F.Id("n2"))),
                    Call("F", F.Id("n2")))), Sp, Eq, Sp,
            Call("app", Call("RewSubst", F.Id("w")), F.Id("phi")), Dot));

    private static Formula ShiftFormula() =>
        Disp(Seq(
            F.Id("shift"), Colon, Sp,
            Call("Hom", Call("F", F.Id("n")), Call("F", F.Id("n"))),
            Sp, Eq, Sp, Call("app", F.Id("RewShift")), Dot));

    private static Formula FreeFormula() =>
        Disp(Seq(
            F.Id("free"), Colon, Sp,
            Call("Hom", Call("F", Seq(F.Id("n"), Plus, D(1))), Call("F", F.Id("n"))),
            Sp, Eq, Sp, Call("app", F.Id("RewFree")), Dot));

    private static Formula ShiftsFormula() =>
        Disp(Seq(
            F.Id("shifts"), Colon, Sp,
            new Formula.TypeArrow(Call("List", Call("F", F.Id("n"))), Call("List", Call("F", F.Id("n")))),
            Sp, Eq, Sp, Call("map", F.Id("shift")), Dot));

    private static Formula ShiftsNilFormula() =>
        Disp(Seq(
            Call("shifts", EmptyList()), Sp, Eq, Sp, EmptyList(), Dot));

    private static Formula ShiftsConsFormula() =>
        Disp(Seq(
            Call("shifts", Call("cons", F.Id("phi"), F.Id("Gamma"))), Sp, Eq, Sp,
            Call("cons", Call("shift", F.Id("phi")), Call("shifts", F.Id("Gamma"))), Dot));

    private static Formula ShiftsNegFormula() =>
        Disp(Seq(
            Call("shifts", Call("negList", F.Id("Gamma"))), Sp, Eq, Sp,
            Call("negList", Call("shifts", F.Id("Gamma"))), Dot));

    private static Formula EmbFormula() =>
        Disp(Seq(
            F.Id("emb"), Colon, Sp,
            Call("Hom", Call("O", F.Id("n")), Call("F", F.Id("n"))),
            Sp, Eq, Sp, Call("app", F.Id("RewEmb")), Dot));

    private static Formula SubstNotationFormula() =>
        Disp(Seq(
            F.Id("phi"), Slash, OpenBracket, F.Id("w"), CloseBracket,
            Sp, Mapsto, Sp, F.Id("phi"), Sp, F.Id("subst"), Sp, F.Id("w"), Dot));

    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);

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
