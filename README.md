# xia SQL 检测规则说明

本项目是一个基于 Burp Montoya API 的 SQL 注入检测插件。本文档聚焦当前版本的检测规则与判定条件。

## 1. 扫描目标范围

- URL 参数：`HttpParameterType.URL`
- Body 参数：`HttpParameterType.BODY`
- JSON 参数：`HttpParameterType.JSON`
- Path 段：如 `/user/path/admin` 会提取为 `path[0]=user`、`path[1]=path`、`path[2]=admin`
- Header：仅在勾选 `测试Header` 时启用

### Header 黑名单

黑名单内的 Header 不参与测试。

- 内置保留黑名单：`host`、`content-length`、`transfer-encoding`
- UI 可配置黑名单（默认）：`Connection,Accept,Accept-Language`

### Path / Header 去重

- Path 去重：仅在同一 `host` 内生效；同一 `host` 下相同 Path 段值只测试一次
- Header 去重：仅在同一 `host` 内生效；同一 `host` 下相同 Header 名只测试一次
- 点击 `清空列表` 会同时清空 Path / Header 去重缓存

## 2. 过滤逻辑

### 白名单过滤

启用白名单后，仅扫描命中目标域名规则的请求。

### 静态文件过滤

默认跳过扩展名：

`jpg`、`png`、`gif`、`css`、`js`、`pdf`、`mp3`、`mp4`、`avi`

### 请求去重

按 `url基础路径 + 参数名集合 + method` 计算 MD5，避免重复扫描。

## 3. 节流

- 全局发包间隔：默认 `100ms`，可在 UI 调整
- 单请求慢阈值：`SINGLE_REQUEST_SLOW_MS = 4000ms`

## 4. 注入检测规则

以下规则都在同一参数维度内执行。

### 4.1 单引号拼接注入

发送四个 payload：

- `value'`
- `value''`
- `value'''`
- `value''''`

记响应体长度为 `len1~len4`，命中条件：

1. `|len2 - len4| <= 5`
2. `|len1 - len3| <= 5`
3. `|len1 - len2| >= 4`

命中标记：`✔ 单引号拼接注入`

### 4.2 数字型注入

仅对数字参数执行。

1. `value-0-0-0` 与原始响应文本相似度 `> 0.90`
2. 再发 `value-abc`，结合相似度规则判定

命中标记：`✔ 数字型注入`

### 4.3 order 注入（逗号规则）

按 `value,0`、`value,1`、`value,2` 等变体组合，通过 Jaccard 相似度规则判定。

命中标记：`✔ order注入`

### 4.4 模糊查询注入

三步检测：

1. `poc1 = value'`，要求与原始响应长度差 `> 10`
2. `poc2 = value'+or+1=1--+`
3. `poc3 = value'+or+1=2--+`

判定核心：`sim(poc2, poc3) < 0.90`

命中标记：`✔ 模糊查询注入`

### 4.5 反引号注入

三步检测：

1. `poc1 = value\``，要求与原始响应长度差 `> 10`
2. `poc2 = value\`and+sleep(2)--+`，要求与基线时间差 `>= 2000ms`
3. `poc3 = value\`and+sleep(5)--+`，要求与基线时间差 `< 6000ms`

命中标记：`✔ 反引号注入`

### 4.6 报错注入

对基础引号 payload 的响应体匹配正则规则（可在 UI 维护）。

命中标记：`✔ 报错:<pattern>`

### 4.7 表达式注入（exp）

payload：

- `'||exp(200)||'`
- `'||exp(11111)||'`

判定条件：

1. `|len(exp200) - len(base)| <= 15`
2. `|len(exp11111) - len(exp200)| >= 15`

命中标记：`✔ 表达式注入(exp)`

### 4.8 表达式注入（除零）

payload：

- `'||1/0||'`
- `'||1/1||'`

判定条件：

1. `|len(1/1) - len(base)| <= 10`
2. `|len(1/1) - len(1/0)| >= 10`

命中标记：`✔ 表达式注入(除零)`

### 4.9 括号模糊查询延时注入

两步检测：

1. `poc1 = value'` 与 `poc2 = value''`
2. `poc3 = value')+and+sleep(5)--+`

判定条件：

- `|len(value') - len(value'')| <= 5`
- `cost(poc3) - cost(base) >= 5000ms`

命中标记：`✔ 括号模糊查询延时注入`

### 4.10 自定义 payload 检测

从 `xia_SQL_diy_payload.ini` 读取并发送用户自定义 payload。支持：

- 空格 URL 编码
- 参数值置空

命中可来自相似度规则或报错规则。

## 5. 执行策略

- 同一参数按规则顺序依次检测
- 任一规则命中后，当前参数会立即得到命中结果
- 命中后仍会继续执行 `div` 检测
- `div` 之后会跳过其余后续检测，包括 `exp`、括号模糊查询延时注入、自定义 payload
- 请求明显偏慢时，会跳过部分后续重型检测

## 6. UI 相关默认值

- `测试Path`：默认开启
- `测试Header`：默认关闭
- 全局发包间隔：默认 `100ms`
- Header 黑名单输入框默认值：`Connection,Accept,Accept-Language`

## 7. 结果标记与查看

- 主表 `state` 会在完成后显示 `end!`，命中会追加 `✔`
- 详情表会对命中 payload 行打标签并高亮
- 选中主表请求后，右侧可查看对应 Request/Response
