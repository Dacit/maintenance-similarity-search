source("setup.R")

data <- data.frame(read.csv(file="data/clones_hol.csv", head=TRUE)) %>%
  rowwise() %>%
  mutate(
    judgement=
if (category %in% c("verbatim", "identical", "equivalent", "equal", "generalization", "isomorphic")) "Duplicate"
else if (category %in% c("shared", "dual")) "Similar"
else if (category %in% c("different")) "Different"
else "NONE")

table <-
  data %>% group_by(category) %>% summarise(n=n())
data %>% filter(score >= 0.90) %>% group_by(judgement) %>% summarise(n=n())

ggplot(data, aes(x=factor(judgement, levels=c("Different", "Similar", "Duplicate")), y=score)) +
  geom_boxplot(color=pubr_palette(2)[2], outlier.shape = 1) +
  stat_boxplot(geom = 'errorbar', width = 0.2, color=pubr_palette(2)[2]) +
  coord_flip() +
  ylim(c(1, 0.85))+
  ylab("Similarity") +
  xlab(NULL) +
  theme_pubr()
