source("setup.R")

data <- data.frame(read.csv(file= "data/ranks.csv", head=TRUE))

ggplot(data, aes(x=factor(name, 
levels=c(
  "mk_config l1 (ml, IDF, (k {typ=1,cls=28,thm=1,cnst=37}), p1, d1)",
  "mk_config (lr {lmt=10,dp=0.85}) (ml, IDF, (k {typ=1,cls=1,thm=1,cnst=2}), p2, dw)"
),
labels = c("Singleton", "Community")), y=rank)) +
  geom_boxplot(color=pubr_palette(2)[2], outlier.shape = 1) +
  stat_boxplot(geom = 'errorbar', width = 0.2, color=pubr_palette(2)[2]) +
  coord_flip() +
  ylim(c(1, 81)) +
  scale_y_continuous(breaks=c(1, 5, 10, 20, 40, 60, 80)) +
  ylab("Rank") +
  xlab(NULL) +
  theme_pubr()