using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Measure;

internal sealed class ProperSupportMarginalGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Measure/ProperSupportMarginalGluing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/finner1992holder");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized factorizations of deleted-coordinate marginals determine one common " +
        "factorization of all proper-support rows.",
        H("Gluing common profiles from coordinate marginals"),
        Blocks(
            Describe.Lean(DescribeId.Create("common-profiles-deleted-marginals"),
                DeclarationHandle.Create(Prefix + "exists_common_profiles_of_deleted_marginal_factorizations"),
                H("Proper-support marginal gluing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let I be an arbitrary finite type and J any type, with X_i arbitrary measurable spaces, " +
                        "and mu_i probability measures. Write mu for their actual dependent " +
                        "product law. Fix an active finite coordinate set A and finite supports " +
                        "S_j contained in A, with S_j different from A for every j. Let f_j be " +
                        "measurable ENNReal functions on the full product that depend only on " +
                        "S_j. Their original masses m_j=integral_mu(f_j) are positive and finite.")),
                    Paragraph(Text(
                        "For every k in A, suppose there is a measurable family g_i^(k) on " +
                        "X_i, each of integral one under mu_i, such that, for every j, the " +
                        "marginal obtained by integrating f_j over coordinate k equals " +
                        "m_j times the product of g_i^(k)(x_i) over i in S_j with k removed, " +
                        "mu-almost everywhere. The different k may use different families.")),
                    Paragraph(Text(
                        "Then there exists one measurable family h_i, each with integral_mu_i " +
                        "h_i equal to one, such that every original row f_j equals m_j times " +
                        "the product of the same h_i(x_i) over S_j, mu-almost everywhere. " +
                        "No coordinate coverage, incidence weights, positive conditional " +
                        "masses, finite alphabets, topologies or countable-generation " +
                        "assumptions are imposed. Empty supports and index types are retained " +
                        "whenever the displayed hypotheses hold. If J is infinite, each row may " +
                        "have its own exceptional null set. Zeros on positive-measure " +
                        "sets and infinite values on null sets are allowed.")),
                    Paragraph(Text(
                        "First normalize f_j by its positive finite original mass. For each " +
                        "coordinate occurring in some support, choose an incident row and " +
                        "take its one-coordinate marginal, integrating all other coordinates. " +
                        "Evaluate that marginal at a fixed anchor with this coordinate " +
                        "inserted. Marginal insertion gives a unit integral. An unused " +
                        "coordinate receives the constant profile one.")),
                    Paragraph(Text(
                        "To recover row j, choose k in A outside S_j. Its k-marginal is " +
                        "pointwise the original normalized row. For each i in S_j, compare " +
                        "the chosen incident row with its k-deleted factorization. Integrate " +
                        "every coordinate except i. Measurable marginal integration preserves " +
                        "the almost-everywhere equality; unit coordinate integrals leave " +
                        "exactly g_i^(k)(x_i). Since k differs from i, the repeated integration " +
                        "over k is absorbed. Thus every selected h_i agrees with g_i^(k) " +
                        "under the original product law. A finite intersection of these " +
                        "equalities reconstructs row j. Multiplication by m_j restores " +
                        "the original normalization.")),
                    Paragraph(Text(
                        "Bennett and Oh, Section 2.1, use this proper-support assembly within " +
                        "an induction for Finner stability. The statement here is the exact " +
                        "marginal gluing implication for measurable ENNReal factors. It " +
                        "assumes the concrete deleted-marginal factorizations. Finner " +
                        "saturation alone is not a hypothesis from which this declaration " +
                        "derives those factorizations. The full balanced Finner equality " +
                        "classification additionally requires their derivation by dimension " +
                        "induction and a treatment of rows with full active support."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-finner-equality-common-profiles"),
                DeclarationHandle.Create(Prefix + "finner_equality_iff_common_profiles"),
                H("The complete balanced Finner equality criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let I and J be arbitrary finite types, X_i arbitrary measurable spaces, " +
                        "and mu_i probability measures. Every measurable ENNReal row f_j on the " +
                        "dependent product depends only on its finite support S_j. Its mass " +
                        "m_j under the original product measure mu is strictly positive and finite. " +
                        "The real weights w_j are strictly positive, and the sum of w_j over " +
                        "rows containing coordinate i equals one for every i. The coordinate " +
                        "incidence patterns are separated: if a and b belong to exactly the same " +
                        "row supports, then a=b.")),
                    Paragraph(Text(
                        "Then integral_mu(product_j f_j(x)^w_j)=product_j m_j^w_j if and only " +
                        "if there is one family of measurable ENNReal functions h_i on X_i, " +
                        "each of integral one under mu_i, such that for every row j, " +
                        "f_j(x)=m_j product_{i in S_j} h_i(x_i) mu-almost everywhere. " +
                        "The law in the hypothesis, every mass, and every row equality is the " +
                        "same original product law. There are no conditions on conditional slice " +
                        "masses, finite alphabets, pointwise positivity, distinct row supports, " +
                        "or coordinate topologies. Empty types and supports, repeated supports, " +
                        "weight-one rows, unrestricted positive weights on empty supports, " +
                        "positive-measure zeros and infinite values on null sets are retained.")),
                    Paragraph(Text(
                        "Normalize every row by its positive finite mass. Induct on a finite " +
                        "active coordinate set while keeping the ambient product law fixed. " +
                        "Marginal integration preserves unit mass. The marginal Finner estimate " +
                        "and Finner for the deleted rows sandwich the weighted-product integral " +
                        "of every coordinate-deleted family at one. Its supports lose exactly " +
                        "that coordinate; balance and incidence separation persist on the " +
                        "remaining active set. The smaller-set conclusion therefore supplies " +
                        "the concrete marginal factorizations required by proper-support gluing.")),
                    Paragraph(Text(
                        "At each active set, first obtain the proper-row implication from the " +
                        "smaller-set conclusions. For at least two active coordinates, remove " +
                        "the common full-support incidence mask. Separation and strictly positive " +
                        "weights force the remaining incidence budget r to be strictly positive. " +
                        "Divide proper-row weights by r and denote their weighted product by Q. " +
                        "Finner gives integral Q at most one; a global Holder bound and the " +
                        "original saturation give (integral Q)^r at least one. Thus integral Q " +
                        "is one. The proper-row implication reconstructs Q as the product of " +
                        "the common coordinate profiles. Normalized finite Holder applied to Q " +
                        "and the full rows identifies every full row with Q almost everywhere.")),
                    Paragraph(Text(
                        "For an empty active set, unit rows depending on no coordinates are " +
                        "constant one. For a singleton active set, discard those empty-support " +
                        "unit rows and use normalized Holder on the incident rows. A coordinate " +
                        "section of a supported representative gives the measurable unit profile; " +
                        "no almost-everywhere equality is restricted to a chosen anchor. " +
                        "For the converse, finite product interchange and balance combine the " +
                        "powered row representations into one product of the coordinate profiles. " +
                        "Tonelli and their unit integrals give saturation. Positive finite scalar " +
                        "normalization restores exactly the original masses in both directions. " +
                        "This is the classical equality classification with the stated ENNReal " +
                        "endpoints; no mathematical originality is claimed."))),
                DescribeRole.Theorem))));
}
