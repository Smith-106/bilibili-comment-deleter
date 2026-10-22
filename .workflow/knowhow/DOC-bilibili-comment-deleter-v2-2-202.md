---
title: B站评论删除 v2.2.202
category: usage
createdBy: cleanup
sourceRef: v2.2.202
---
# B站评论批量删除

当前版本 **v2.2.202**。只删除当前登录账号自己的评论。

## 安装

Tampermonkey 安装：

https://raw.githubusercontent.com/Smith-106/bilibili-comment-deleter/main/bilibili-comment-deleter.user.js

打开任意 `*.bilibili.com` 页面后使用。版本号应是 v2.2.202。停用手工改过的旧副本。

## 三个来源

- AICU：能查到的自己的评论，不是官方实时全量。
- 官方历史：最近看过的视频，不是全部历史。
- 导入：本工具导出的 JSON / CSV。

## 删除结果

`code=0` 只表示受理。开回查才会再确认；没开回查时，受理的记为待确认。番剧 type=11 的 csrf 放在查询参数里。

## 文档

- 文档站：`docs/index.html`（GitHub Pages）
- 变更记录：仓库根目录 `README.md`
