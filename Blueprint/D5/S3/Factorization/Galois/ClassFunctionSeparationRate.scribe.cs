using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ClassFunctionSeparationRateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/ClassFunctionSeparationRate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite class-function separation is exactly computable from conjugacy classes.",
        H("Class-Function Separation Rate"),
        Blocks(
            Definition(
                "conjugacy-invariant-target",
                "IsConjugacyInvariantTarget",
                "A conjugacy-invariant target",
                InvariantTargetFormula(),
                "A target is constant on every Mathlib conjugacy class."),
            Definition(
                "conjugacy-invariant-target-pair",
                "AreConjugacyInvariantTargets",
                "A conjugacy-invariant target pair",
                InvariantPairFormula(),
                "Both readings in the pair are class functions."),
            Definition(
                "separation-set",
                "separationSet",
                "The finite separation event",
                SeparationSetFormula(),
                "The named event contains exactly the elements where the readings differ."),
            Definition(
                "finite-group-success-rate",
                "finiteGroupSuccessRate",
                "The exact uniform success rate",
                SuccessRateFormula(),
                "The rate is the rational cardinality ratio of the separation event."),
            Definition(
                "conjugacy-class-separates",
                "conjugacyClassSeparates",
                "A separating conjugacy class",
                ClassSeparatesFormula(),
                "A class is selected when it contains at least one successful element."),
            Definition(
                "separating-conjugacy-classes",
                "separatingConjugacyClasses",
                "The separating conjugacy classes",
                SeparatingClassesFormula(),
                "This named finite set filters all conjugacy classes by separation."),
            Definition(
                "conjugacy-class-separation-count",
                "conjugacyClassSeparationCount",
                "The conjugacy-class separation count",
                ClassCountFormula(),
                "The count sums the cardinalities of all selected classes."),
            Describe.Lean(
                DescribeId.Create(
                    "separation-set-membership-is-conjugacy-invariant"),
                DeclarationHandle.Create(
                    Prefix + "separation_set_membership_is_conjugacy_invariant"),
                H("The separation event is a union of conjugacy classes"),
                StatementSource.FromAuthor(MembershipFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If both targets are class functions, conjugate elements either both "
                        + "belong to the separation event or both lie outside it."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "finite-group-success-rate-equals-conjugacy-class-count"),
                DeclarationHandle.Create(
                    Prefix + "finite_group_success_rate_eq_conjugacy_class_count"),
                H("Uniform success is a conjugacy-class cardinality ratio"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's conjugacy classes partition the finite carrier. Since the "
                            + "separation predicate is constant on each class, fiberwise "
                            + "cardinality reduces the numerator to a sum of whole classes.")),
                    Paragraph(Text(
                        "The proof needs only a finite monoid, weakening the finite-group "
                            + "structure from the Galois source without changing its instance.")),
                    Paragraph(Text(
                        "This closes only the finite counting half. Pinned Mathlib has no "
                            + "Chebotarev density theorem, so no prime-ideal frequency transfer "
                            + "is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-carrier-has-zero-success-rate"),
                DeclarationHandle.Create(Prefix + "empty_carrier_has_zero_success_rate"),
                H("The empty finite carrier has zero totalized rate"),
                StatementSource.FromAuthor(EmptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On Fin zero the event is empty and rational zero divided by zero is "
                        + "totalized to zero. A monoid carrier itself cannot realize this case."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("monoid-carrier-is-nonempty"),
                DeclarationHandle.Create(Prefix + "monoid_carrier_is_nonempty"),
                H("Every monoid carrier is nonempty"),
                StatementSource.FromAuthor(NonemptyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity element excludes an empty group or monoid carrier."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("identical-targets-have-zero-success-rate"),
                DeclarationHandle.Create(
                    Prefix + "identical_targets_have_zero_success_rate"),
                H("Identical targets have zero success rate"),
                StatementSource.FromAuthor(IdenticalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This includes identity, constant, and zero maps when used on both sides."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "trivial-group-distinct-targets-have-full-success-rate"),
                DeclarationHandle.Create(
                    Prefix + "trivial_group_distinct_targets_have_full_success_rate"),
                H("Distinct constant targets have full rate on the trivial group"),
                StatementSource.FromAuthor(TrivialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sole group element receives different Boolean readings, so the "
                        + "successful set has cardinality one out of one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("conjugacy-invariance-is-necessary"),
                DeclarationHandle.Create(Prefix + "conjugacy_invariance_is_necessary"),
                H("Conjugacy invariance is necessary for the class-union step"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In the symmetric group on three letters, evaluation at zero separates "
                        + "one transposition from a conjugate transposition. The comparison "
                        + "target is constant and conjugacy invariant, so the missing premise "
                        + "is isolated to the nonconstant target."))),
                DescribeRole.Lemma))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
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

    private static Formula Target(Formula target, Formula value) =>
        Seq(target, Open, value, Close);

    private static Formula Rate(Formula first, Formula second) =>
        Call(F.Id("SuccessRate"), first, second);

    private static Formula Count(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula InvariantTargetFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula tau = F.Id("tau");
        Formula target = F.Id("f");
        return Disp(Seq(
            Call(F.Id("IsConj"), sigma, tau), Sp, Rightarrow, Sp,
            Target(target, sigma), Sp, Eq, Sp, Target(target, tau), Dot));
    }

    private static Formula InvariantPairFormula() =>
        Disp(Seq(
            Call(F.Id("ClassFunction"), F.Id("f")), Sp, Land, Sp,
            Call(F.Id("ClassFunction"), F.Id("g")), Dot));

    private static Formula SeparationSetFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula first = F.Id("f");
        Formula second = F.Id("g");
        Formula subscript = Seq(first, Comma, second);
        return Disp(Seq(
            new Formula.Subscript(F.Id("U"), subscript), Sp, Eq, Sp,
            OpenBrace, sigma, Sp, InMacro, Sp, F.Id("G"), Sp, Mid, Sp,
            Target(first, sigma), Sp, Neq, Sp, Target(second, sigma), CloseBrace, Dot));
    }

    private static Formula SuccessRateFormula()
    {
        Formula first = F.Id("f");
        Formula second = F.Id("g");
        Formula separation = new Formula.Subscript(
            F.Id("U"), Seq(first, Comma, second));
        return Disp(Seq(
            Rate(first, second), Sp, Eq, Sp,
            new Formula.Fraction(Count(separation), Count(F.Id("G"))), Dot));
    }

    private static Formula ClassSeparatesFormula()
    {
        Formula sigma = F.Id("sigma");
        return Disp(Seq(
            Call(F.Id("Separates"), F.Id("C")), Sp, Iff, Sp,
            Exists, Sp, sigma, Sp, InMacro, Sp, F.Id("C"), Comma, Sp,
            Target(F.Id("f"), sigma), Sp, Neq, Sp, Target(F.Id("g"), sigma), Dot));
    }

    private static Formula SeparatingClassesFormula()
    {
        Formula conjClass = F.Id("C");
        return Disp(Seq(
            F.Id("S"), Sp, Eq, Sp, OpenBrace, conjClass, Sp, InMacro, Sp,
            Call(F.Id("ConjClasses"), F.Id("G")), Sp, Mid, Sp,
            Call(F.Id("Separates"), conjClass), CloseBrace, Dot));
    }

    private static Formula ClassCountFormula() =>
        Disp(Seq(
            F.Id("N"), Sp, Eq, Sp, Sum, Sp, new Formula.Subscript(
                F.Id("C"), Seq(F.Id("C"), Sp, InMacro, Sp, F.Id("S"))), Sp,
            Count(F.Id("C")), Dot));

    private static Formula MembershipFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula tau = F.Id("tau");
        Formula separation = new Formula.Subscript(
            F.Id("U"), Seq(F.Id("f"), Comma, F.Id("g")));
        return Disp(Seq(
            Call(F.Id("IsConj"), sigma, tau), Sp, Rightarrow, Sp,
            Open, sigma, Sp, InMacro, Sp, separation, Close, Sp, Iff, Sp,
            Open, tau, Sp, InMacro, Sp, separation, Close, Dot));
    }

    private static Formula MainFormula() =>
        Disp(Seq(
            Rate(F.Id("f"), F.Id("g")), Sp, Eq, Sp,
            new Formula.Fraction(F.Id("N"), Count(F.Id("G"))), Dot));

    private static Formula EmptyFormula() =>
        Disp(Seq(
            Call(F.Id("SuccessRateFin"), D(0), F.Id("f"), F.Id("g")), Sp,
            Eq, Sp, D(0), Dot));

    private static Formula NonemptyFormula() =>
        Disp(Seq(Call(F.Id("Nonempty"), F.Id("G")), Dot));

    private static Formula IdenticalFormula() =>
        Disp(Seq(Rate(F.Id("f"), F.Id("f")), Sp, Eq, Sp, D(0), Dot));

    private static Formula TrivialFormula() =>
        Disp(Seq(Rate(F.Id("true"), F.Id("false")), Sp, Eq, Sp, D(1), Dot));

    private static Formula NecessityFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula tau = F.Id("tau");
        return Disp(Seq(
            Exists, Sp, sigma, Comma, Sp, tau, Sp, InMacro, Sp, F.Id("S3"), Comma, Sp,
            Call(F.Id("IsConj"), sigma, tau), Sp, Land, Sp,
            Target(F.Id("f"), sigma), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            Target(F.Id("f"), tau), Sp, Eq, Sp, D(0), Dot));
    }
}
